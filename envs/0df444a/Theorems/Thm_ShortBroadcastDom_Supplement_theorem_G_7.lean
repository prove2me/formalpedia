-- Prove2me | Theorems.Thm_ShortBroadcastDom_Supplement_theorem_G_7
-- name    : ShortBroadcastDom.Supplement.theorem_G_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:46:21.727815+00:00
-- url     : https://prove2.me/theorems/4cab5f16-32e6-4c98-8b74-35046bdb2f34
-- title:
--   Theorem G.7 — coefficient three for domination at subgraph density $a<8/7$, with $\delta_{17/15}=5/8482$
-- statement:
--   Let $1\le a<8/7$ be rational. There is a rational $\delta_a>0$ with the following property. Let $G$ be a graph every subgraph of which has a ratio of edges to vertices of at most $a$, let $F,Z,R_0$ and $c$ be the transformation of App. G.1, and let $x\in[0,1]^Z$ be any feasible fractional cover of $R_0$ in $G[Z]$ with
--
--   $$
--   \mathcal C(x)\le(1+\delta_a)\,C^*,
--   $$
--
--   where $C^*$ is the minimum cost of a fractional cover of $R_0$ in $G[Z]$. Then $F\cup D$ is a dominating set of $G$ with $|F\cup D|\le3\gamma_f(G)$. The sets $F$ and $R_0$ and the costs $c$ are computed in a constant number of broadcast rounds with messages of constant size, and so is $F\cup D$ once $x$ is given. For $a=17/15$ the value $\delta_a=5/8482$ suffices.
--
--   Any fractional solver of accuracy $\delta_a$ therefore yields the optimal coefficient three on such graphs, for instance on planar graphs of girth at least 17.
--
--   **Formalization Note** "Messages of constant size" is a bit bound fixed before the graph and the identifier exponent. The computability claims are two broadcast algorithms: the first outputs membership in $F$, membership in $R_0$ and the cost; the second, given $x_v$, outputs membership in $F\cup D$.
--
--   Differences from the source:
--   - reading: broadcast CONGEST (each vertex receives its neighbours' messages) → the multiset of the neighbours' messages, without port numbers; reason: gives the algorithm less information, so the existence statement is at least as strong; a sender can prepend its O(log(n+1))-bit identifier
--   - encoding: feasible fractional cover of R0 in G[Z]; C* its minimum cost → IsFeasibleOn G Z R₀ x (constraints over N[r] ∩ Z); C* = tauOn G Z R₀ c; reason: the closed neighbourhood of a demand lies in Z (p.89), so the constraints are those of G[Z]
--   - encoding: computed in a constant number of broadcast rounds with messages of constant size → broadcast algorithms with a fixed round count and messages of at most m bits for all graphs and identifier exponents; reason: direct transcription in the base model
--   - encoding: for a = 17/15, the value δa = 5/8482 suffices → δ = 5/8482 whenever a = 17/15; reason: the same property for that value
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. G.1, p.94 (PDF p.97), Theorem G.7; transformation p.89, rounding p.90 (PDF pp.92–93)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd
import Definitions.Def_ShortBroadcastDom_tauOn
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_ShortBroadcastDom_RoundingData
import Definitions.Def_ShortBroadcastDom_Supplement_g1Sel
import Definitions.Def_ShortBroadcastDom_Supplement_g1Round

namespace ShortBroadcastDom.Supplement

open ShortBroadcastDom

/-- **Theorem G.7 (coefficient three at a fixed density below eight sevenths).** Amiri, Siebertz,
Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix f4dc98d2), App. G.1,
p.94 (PDF 97): "Let 1 ≤ a < 8/7 be rational. There is a rational δa > 0 with the following
property. Let G be a graph every subgraph of which has a ratio of edges to vertices of at most a,
let F, Z, R0, and c be as above, and let x ∈ [0, 1]^Z be any feasible fractional cover of R0 in
G[Z] with C(x) ≤ (1 + δa)C∗. Then F ∪ D is a dominating set of G of size at most 3γf(G). The sets F
and R0 and the costs c are computed in a constant number of broadcast rounds with messages of
constant size, and so is F ∪ D once x is given. For a = 17/15, the value δa = 5/8482 suffices."
`F, Z, R₀, c` are the transformation of p.89 and `D` the rounding of p.90.

**Formalization Note** For the given `a`, one rational `δ > 0`, equal to `5/8482` when
`a = 17/15`, works for every graph `G` of subgraph density at most `a` and every `x ∈ [0, 1]^Z`
feasible for `R₀` (`IsFeasibleOn G Z R₀ x`, constraints `∑_{v ∈ N[r] ∩ Z} x_v ≥ 1`; a demand's
closed neighbourhood lies in `Z`, so this is the program of `G[Z]`) with
`C(x) = ∑_{v ∈ Z} c(v)x_v ≤ (1 + δ)C*`, where `C* = tauOn G Z R₀ c` is the minimum cost of a
fractional cover of `R₀` by candidates in `Z`. The two computability claims are broadcast algorithms
fixed before the graph: the first (local input `Unit`) outputs membership in `F`, membership in `R₀`
and the cost (on `Z`); the second (local input `x_v`) outputs membership in `F ∪ D`. "Messages of
constant size" is a bit bound `m` independent of the graph and of the identifier exponent `k`:
`MsgBounded … m 1` bounds every message by `m(⌊log₂ 1⌋ + 1) = m` bits. -/
theorem theorem_G_7 (a : ℚ) (ha1 : 1 ≤ a) (ha : a < 8 / 7) :
    ∃ δ : ℚ, 0 < δ ∧ (a = 17 / 15 → δ = 5 / 8482) ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SubgraphDensityLE (a : ℝ) G → ∀ x : V → ℝ, IsFeasibleOn G (g1Z G) (g1R0 G) x →
          g1CostOf G x ≤ (1 + (δ : ℝ)) * tauOn G (g1Z G) (g1R0 G) (g1Cost G) →
            DominatesSet G Finset.univ (g1F G ∪ g1D G x) ∧
            ((g1F G ∪ g1D G x).card : ℝ) ≤ 3 * fracDom G) ∧
      (∃ alg : BroadcastAlg Unit (Bool × Bool × ℕ), ∃ T m : ℕ,
        ∀ (k : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ), ValidIds k (Fintype.card V) id → SubgraphDensityLE (a : ℝ) G →
            MsgBounded alg G id (fun _ => ()) T m 1 ∧
            ∀ v, ((alg.output G id (fun _ => ()) T v).1 = true ↔ v ∈ g1F G) ∧
              ((alg.output G id (fun _ => ()) T v).2.1 = true ↔ v ∈ g1R0 G) ∧
              (v ∈ g1Z G → ((alg.output G id (fun _ => ()) T v).2.2 : ℝ) = g1Cost G v)) ∧
      (∃ alg : BroadcastAlg ℝ Bool, ∃ T m : ℕ,
        ∀ (k : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ) (x : V → ℝ), ValidIds k (Fintype.card V) id →
          SubgraphDensityLE (a : ℝ) G → IsFeasibleOn G (g1Z G) (g1R0 G) x →
            MsgBounded alg G id x T m 1 ∧ alg.outSet G id x T = g1F G ∪ g1D G x) := by sorry

end ShortBroadcastDom.Supplement
