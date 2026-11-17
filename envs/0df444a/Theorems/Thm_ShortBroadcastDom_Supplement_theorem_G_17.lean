-- Prove2me | Theorems.Thm_ShortBroadcastDom_Supplement_theorem_G_17
-- name    : ShortBroadcastDom.Supplement.theorem_G_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:47:09.106649+00:00
-- url     : https://prove2.me/theorems/816cf55d-eb0a-4e4c-9c14-6a2913180b2d
-- title:
--   Theorem G.17 — coefficient two for total domination at subgraph density $a<9/8$, and on planar graphs of girth $\ge19$ (optimal)
-- statement:
--   1. Let $1\le a<9/8$ be rational. There is a rational $\delta'_a>0$ with the following property. Let $G$ be an isolate-free graph every subgraph of which has a ratio of edges to vertices of at most $a$, let $F,Z,K$ and $c$ be the transformation of App. G.3, and let $x\in[0,1]^K$ be any feasible fractional solution with $\mathcal C(x)\le(1+\delta'_a)C^*$. Then $F\cup D$ is a total dominating set of $G$ with
--   $$|F\cup D|\le2\,\gamma_{t,f}(G).$$
--   The sets $F,Z,K$ and the costs are computed in a constant number of broadcast rounds, and so is $F\cup D$ once $x$ is given. For $a=19/17$ the value $\delta'_a=1/62514$ suffices.
--   2. There is a deterministic constant-round broadcast CONGEST algorithm that returns a total dominating set of size at most $2\gamma_{t,f}(G)$ on every isolate-free planar graph $G$ of girth at least $19$. The coefficient two is optimal on this class, also against the integral optimum $\gamma_t(G)$.
--
--   **Formalization Note** In (i) $x$ is extended by zero outside $K$ and feasibility means $\sum_{v\in N(r)\cap K}x_v\ge1$ for every $r\in Z$; $D$ depends on the identifiers through the requests. Optimality is stated as: for every $\varepsilon>0$, every $T$ and every deterministic $T$-round LOCAL algorithm there is an isolate-free planar graph of girth at least $19$, with identifiers $1,\dots,n$ and $n$ known, on which the output is not a total dominating set or exceeds $(2-\varepsilon)|S|$ for some total dominating set $S$.
--
--   Differences from the source:
--   - reading: broadcast CONGEST (each vertex receives its neighbours' messages) → the multiset of the neighbours' messages, without port numbers; reason: gives the algorithm less information, so the existence statement is at least as strong; a sender can prepend its O(log(n+1))-bit identifier
--   - reading: constant-round, identifiers and messages of O(log(n+1)) bits → ∃ algorithm ∃ T, ∀ k ∃ c: identifiers < (n+1)^k, messages ≤ c(⌊log₂ n⌋+1) bits; reason: the algorithm and its round count are independent of the identifier constant k; this is the stronger quantifier order
--   - reading: deterministic T-round LOCAL algorithm (after T rounds a vertex knows the labelled radius-(T+1) ball with identifiers, degrees, port numbers, and n) → a BroadcastAlg without message bound, local input n, identifiers a bijection onto {1,…,n}, output after T rounds; reason: full-information broadcast with distinct identifiers simulates the paper's convention in T+2 rounds with identifier-ordered ports, so the statement for every T implies the paper's
--   - encoding: x ∈ [0,1]^K extended by zero; C* the optimum of the program → x_v = 0 off K, constraints over N(r) ∩ K; C* = tauRel Z (N(·) ∩ K) c; reason: costs vanish off K and are nonnegative (Lemma G.11(ii)), so the value is the optimum over K
--   - encoding: girth at least 19 → 19 ≤ SimpleGraph.egirth in ℕ∞; reason: Mathlib's extended-natural girth gives acyclic graphs infinite girth, as in the paper
--   - reading: the coefficient two is optimal on this class, also against γt(G) → for every ε > 0, T and deterministic T-round LOCAL algorithm, a witness in the class where the output is not total dominating or exceeds (2−ε)|S| for a total dominating set S; reason: optimality refers to deterministic constant-round algorithms (Proposition F.13 with t = 1); the integral benchmark is the stronger form
--   - reading: 'For a = 19/17, the value δ′a = 1/62514 suffices' printed after (ii) → part of (i): δ' = 1/62514 whenever a = 19/17; reason: δ′a is the constant of (i); the proof of (i) computes it
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. G.3, p.101 (PDF p.104), Theorem G.17; transformation p.96, rounding p.97 (PDF pp.99–100); optimality via Proposition F.13, p.86 (PDF p.89)

import Mathlib
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_ShortBroadcastDom_Supplement_tauRel
import Definitions.Def_ShortBroadcastDom_Supplement_IsTotalDom
import Definitions.Def_ShortBroadcastDom_Supplement_g3Sel
import Definitions.Def_ShortBroadcastDom_Supplement_g3Round
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace ShortBroadcastDom.Supplement

open ShortBroadcastDom

/-- **Theorem G.17 (coefficient two for total domination at a fixed density below nine eighths).**
Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), App. G.3, p.101 (PDF 104): "(i) Let 1 ≤ a < 9/8 be rational. There is a rational
δ′a > 0 with the following property. Let G be an isolate-free graph every subgraph of which has a
ratio of edges to vertices of at most a, let F, Z, K, and c be as above, and let x ∈ [0, 1]^K be
any feasible fractional solution with C(x) ≤ (1 + δ′a)C∗. Then F ∪ D is a total dominating set of G
of size at most 2γt,f(G). The sets F, Z, K and the costs are computed in a constant number of
broadcast rounds, and so is F ∪ D once x is given. (ii) There is a deterministic constant-round
broadcast CONGEST algorithm that returns a total dominating set of size at most 2γt,f(G) on every
isolate-free planar graph G of girth at least 19. The coefficient two is optimal on this class,
also against γt(G). For a = 19/17, the value δ′a = 1/62514 suffices." `F, Z, K, c` are the
transformation of p.96 and `D` the rounding of p.97.

**Formalization Note** Four conjuncts.
1. (i), guarantee: for the given `a`, one rational `δ' > 0`, equal to `1/62514` when `a = 19/17`,
   works for every isolate-free `G` of subgraph density at most `a`, all valid identifiers (the
   requests of Step 3 use them) and every `x ∈ [0, 1]^K` extended by zero (`x_v = 0` off `K`) with
   `∑_{v ∈ N(r) ∩ K} x_v ≥ 1` for every demand `r ∈ Z` and `C(x) ≤ (1 + δ')C*`, where
   `C* = tauRel Z (N(·) ∩ K) c` (costs `c ∈ {0, 1, 2}` by Lemma G.11(ii), so it is the LP optimum).
2. (i), computability: a broadcast algorithm (input `Unit`) outputting membership in `F`, `Z`, `K`
   and the cost, and a broadcast algorithm (input `x_v`) outputting membership in `F ∪ D`, both with
   a fixed round count and `O(log(n + 1))`-bit messages.
3. (ii), algorithm: as in Theorem C, on isolate-free planar graphs with `19 ≤ egirth`.
4. (ii), optimality (Proposition F.13 with `t = 1`): for every `ε > 0`, `T` and deterministic
   `T`-round LOCAL algorithm (a `BroadcastAlg` without message bound, input `n`, identifiers a
   bijection onto `{1, …, n}`; see Theorem F.12 for the simulation of the labelled-ball convention)
   there is an isolate-free planar graph of girth at least `19` on which the output is not a total
   dominating set of size at most `(2 − ε)γ_t(G)`, i.e. it is not total dominating or some total
   dominating set `S` has `(2 − ε)|S| < |D|`. This is the stronger form "against `γ_t`", since
   `γ_{t,f} ≤ γ_t`. -/
theorem theorem_G_17 :
    (∀ a : ℚ, 1 ≤ a → a < 9 / 8 →
      ∃ δ : ℚ, 0 < δ ∧ (a = 19 / 17 → δ = 1 / 62514) ∧
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (k : ℕ) (id : V → ℕ), ValidIds k (Fintype.card V) id → IsolateFree G →
          SubgraphDensityLE (a : ℝ) G → ∀ x : V → ℝ, (∀ v ∈ g3K G, 0 ≤ x v ∧ x v ≤ 1) → (∀ v, v ∉ g3K G → x v = 0) →
          (∀ r ∈ g3Z G, 1 ≤ ∑ v ∈ g3Cov G r, x v) →
          g3CostOf G x ≤ (1 + (δ : ℝ)) * tauRel (g3Z G) (g3Cov G) (g3Cost G) →
            IsTotalDom G (g3F G ∪ g3D G id x) ∧
            ((g3F G ∪ g3D G id x).card : ℝ) ≤ 2 * totFracDom G) ∧
    (∀ a : ℚ, 1 ≤ a → a < 9 / 8 →
      (∃ alg : BroadcastAlg Unit (Bool × Bool × Bool × ℕ), ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ), ValidIds k (Fintype.card V) id → IsolateFree G →
          SubgraphDensityLE (a : ℝ) G →
            MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
            ∀ v, ((alg.output G id (fun _ => ()) T v).1 = true ↔ v ∈ g3F G) ∧
              ((alg.output G id (fun _ => ()) T v).2.1 = true ↔ v ∈ g3Z G) ∧
              ((alg.output G id (fun _ => ()) T v).2.2.1 = true ↔ v ∈ g3K G) ∧
              ((alg.output G id (fun _ => ()) T v).2.2.2 : ℝ) = g3Cost G v) ∧
      (∃ alg : BroadcastAlg ℝ Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ) (x : V → ℝ), ValidIds k (Fintype.card V) id → IsolateFree G →
          SubgraphDensityLE (a : ℝ) G →
          (∀ v ∈ g3K G, 0 ≤ x v ∧ x v ≤ 1) → (∀ v, v ∉ g3K G → x v = 0) →
          (∀ r ∈ g3Z G, 1 ≤ ∑ v ∈ g3Cov G r, x v) →
            MsgBounded alg G id x T c (Fintype.card V) ∧
            alg.outSet G id x T = g3F G ∪ g3D G id x)) ∧
    (∃ alg : BroadcastAlg Unit Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (id : V → ℕ), ValidIds k (Fintype.card V) id → IsolateFree G →
        RobertsonSeymour1986.GM5.IsPlanar G → (19 : ℕ∞) ≤ G.egirth →
          MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
          IsTotalDom G (alg.outSet G id (fun _ => ()) T) ∧
          ((alg.outSet G id (fun _ => ()) T).card : ℝ) ≤ 2 * totFracDom G) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ (T : ℕ) (alg : BroadcastAlg ℕ Bool),
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
        (_ : DecidableRel G.Adj) (id : V → ℕ),
        IsolateFree G ∧ RobertsonSeymour1986.GM5.IsPlanar G ∧ (19 : ℕ∞) ≤ G.egirth ∧
        Function.Injective id ∧ (∀ v, 1 ≤ id v ∧ id v ≤ Fintype.card V) ∧
        (¬ IsTotalDom G (alg.outSet G id (fun _ => Fintype.card V) T) ∨
          ∃ S : Finset V, IsTotalDom G S ∧
            (2 - ε) * (S.card : ℝ) < (alg.outSet G id (fun _ => Fintype.card V) T).card)) := by sorry

end ShortBroadcastDom.Supplement
