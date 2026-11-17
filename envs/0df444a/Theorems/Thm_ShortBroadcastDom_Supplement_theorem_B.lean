-- Prove2me | Theorems.Thm_ShortBroadcastDom_Supplement_theorem_B
-- name    : ShortBroadcastDom.Supplement.theorem_B
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:43:26.266898+00:00
-- url     : https://prove2.me/theorems/9d7b01a9-72a0-48dc-bb02-8148ec37a671
-- title:
--   Theorem B — slack pays for fractional error, and a constant-round transformation gives threshold rounding slack $\delta_a$
-- statement:
--   1. Let a rounding rule have slack $\delta>0$, i.e. $\mathcal C(x)\ge(1+\delta)|D(x)|$ for every feasible $x$. Then every feasible $x$ with $\mathcal C(x)\le(1+\delta)\tau$ satisfies $|D(x)|\le\tau$.
--   2. For every rational $a\ge1$ there is a deterministic broadcast CONGEST algorithm with a constant number of rounds that, on every $G\in\mathcal C_a$, selects a set $F$ and assigns costs $0<c(v)\le 2a+1$ to the candidates $C=V(G)\setminus F$, with demands $R_0=V(G)\setminus N_G[F]$, such that
--      - the threshold rounding of §7.1 with parameter $a$ (sets $W,H,U$ and $D=W\cup H\cup U$) has slack at least $\delta_a$ on the transformed program, for every feasible $x\in[0,1]^C$, where
--      $$\delta_a=\frac1{2a(2a+1)^2}\ \text{if }2a\in\mathbb Z,\qquad \delta_a=\min\Bigl\{\frac{1-\theta}{a(a+1)},\frac{\theta}{\lfloor2a\rfloor+1}\Bigr\}\ \text{otherwise},\quad\theta=2a-\lfloor 2a\rfloor;$$
--      - the transformed fractional optimum satisfies $\tau_{R_0,c}\le(2a+1)\gamma_f(G)-|F|$.
--   3. If $2a\notin\mathbb Z$, the same holds for every $G$ all of whose subgraphs have density at most $a$.
--
--   Combined with the fractional solver, the first assertion lets a fixed solver error disappear from the final approximation coefficient.
--
--   **Formalization Note** The transformation is the shape used in the proof (§7.2: a selected set, the remaining vertices as candidates, the uncovered vertices as demands). Slack is the base definition `HasSlack` over the feasible vectors of the transformed program; the transformed optimum is `tauOn` with candidates $V\setminus F$. One algorithm and round count per $a$, before the identifier exponent and the graph.
--
--   Differences from the source:
--   - generalization: τ is the fractional optimum of the covering program; feasible x of that program → any real τ; an arbitrary type X of solutions with arbitrary maps 𝒞 and |D|; reason: the argument uses only the inequalities; the paper's instance is a special case
--   - reading: a transformation of the instance, computable in a constant number of broadcast rounds → a broadcast algorithm selecting F and costs 0 < c ≤ 2a+1 on C = V∖F, with demands R₀ = V∖N[F]; reason: this is the transformation of the proof (§7.2; F = ∅ and c ≡ 2a+1 in the non-integer case) and of §2.1; existence within this narrower family is at least as strong
--   - reading: threshold rounding → the rule of §7.1 (base RoundingData) with parameter a on the transformed program; reason: the proof (p.48) applies the rounding rule of Lemma 7.1
--   - reading: broadcast CONGEST (each vertex receives its neighbours' messages) → the multiset of the neighbours' messages, without port numbers; reason: gives the algorithm less information, so the existence statement is at least as strong; a sender can prepend its O(log(n+1))-bit identifier
--   - reading: constant-round, identifiers and messages of O(log(n+1)) bits → ∃ algorithm ∃ T, ∀ k ∃ c: identifiers < (n+1)^k, messages ≤ c(⌊log₂ n⌋+1) bits; reason: the algorithm and its round count are independent of the identifier constant k; this is the stronger quantifier order
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.1, p.2 (PDF p.5), Theorem B; proof §7, p.48 (PDF p.51)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd
import Definitions.Def_ShortBroadcastDom_tauOn
import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_ShortBroadcastDom_HasSlack
import Definitions.Def_ShortBroadcastDom_RoundingData
import Definitions.Def_ShortBroadcastDom_Supplement_deltaA

namespace ShortBroadcastDom.Supplement

open ShortBroadcastDom

/-- **Theorem B (paying for fractional error).** Amiri, Siebertz, Wawrzyniak, *Paying for
Fractional Error* (arXiv:2611.02057, sha256 prefix f4dc98d2), §1.1, p.2 (PDF 5): "Let a rounding
rule have slack δ > 0 on a covering program with fractional optimum τ. Then every feasible x with
C(x) ≤ (1 + δ)τ satisfies |D(x)| ≤ τ. For dominating set on graphs of minor density at most a
rational a ≥ 1, there is a transformation of the instance, computable in a constant number of
broadcast rounds, after which threshold rounding has slack at least δa = 1/(2a(2a + 1)²) if 2a is
an integer, δa = min{(1 − θ)/(a(a + 1)), θ/(⌊2a⌋ + 1)} otherwise, where θ = 2a − ⌊2a⌋. The
transformed fractional optimum is at most (2a + 1)γf(G) minus the number of vertices already
selected. If 2a is not an integer, it suffices that all subgraphs have a ratio of edges to vertices
of at most a." Proof: §7, p.48 (PDF 51).

**Formalization Note** Three conjuncts.
1. The first assertion, for every type `X` of feasible solutions, cost `Cx`, size `Dx` and real `τ`.
2. For every rational `a ≥ 1`: a broadcast algorithm (local input `Unit`) whose output after `T`
   rounds is a selection bit and a rational cost. It selects `F`; the transformed instance has
   candidates `C = V \ F`, demands `R₀ = V \ N[F]` and costs `c` with `0 < c ≤ 2a + 1` on `C` (the
   shape of §7.2, which is also the shape of the non-integer case with `F = ∅`). Threshold rounding
   is the rule of §7.1 (base `RoundingData`, parameter `a`, sets `W, H, U`, `D = W ∪ H ∪ U`). Its
   slack is `HasSlack` over every feasible `x ∈ [0, 1]^C` of `R₀` (`IsFeasibleOn`), at `deltaA a`;
   the transformed optimum `τ` is `tauOn G C R₀ c ≤ (2a + 1)γ_f(G) − |F|`. Hypothesis `G ∈ C_a`.
3. The same for rational `a ≥ 1` with `2a ∉ ℤ`, under the subgraph-density hypothesis only.
The algorithm and `T` are fixed before the identifier exponent `k` and the graph; messages have
`O(log(n + 1))` bits. -/
theorem theorem_B :
    (∀ (X : Type) (Cx : X → ℝ) (Dx : X → ℕ) (δ τ : ℝ),
      HasSlack Cx Dx δ → ∀ x, Cx x ≤ (1 + δ) * τ → (Dx x : ℝ) ≤ τ) ∧
    (∀ a : ℚ, 1 ≤ a →
      ∃ alg : BroadcastAlg Unit (Bool × ℚ), ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ), ValidIds k (Fintype.card V) id → InClassC (a : ℝ) G →
          let F : Finset V :=
            Finset.univ.filter fun v => (alg.output G id (fun _ => ()) T v).1 = true
          let cst : V → ℝ := fun v => ((alg.output G id (fun _ => ()) T v).2 : ℝ)
          let R0 : Finset V := Finset.univ.filter fun v => ∀ u ∈ F, v ∉ closedNbhd G u
          MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
          (∀ v, v ∉ F → 0 < cst v ∧ cst v ≤ 2 * (a : ℝ) + 1) ∧
          HasSlack
            (fun x : {x : V → ℝ // IsFeasibleOn G (Finset.univ \ F) R0 x} =>
              RoundingData.cost
                { a := (a : ℝ), C := Finset.univ \ F, R0 := R0, c := cst, x := x.1 })
            (fun x : {x : V → ℝ // IsFeasibleOn G (Finset.univ \ F) R0 x} =>
              (RoundingData.D G
                { a := (a : ℝ), C := Finset.univ \ F, R0 := R0, c := cst, x := x.1 }).card)
            (deltaA (a : ℝ)) ∧
          tauOn G (Finset.univ \ F) R0 cst ≤ (2 * (a : ℝ) + 1) * fracDom G - F.card) ∧
    (∀ a : ℚ, 1 ≤ a → (∀ m : ℤ, 2 * a ≠ m) →
      ∃ alg : BroadcastAlg Unit (Bool × ℚ), ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ), ValidIds k (Fintype.card V) id → SubgraphDensityLE (a : ℝ) G →
          let F : Finset V :=
            Finset.univ.filter fun v => (alg.output G id (fun _ => ()) T v).1 = true
          let cst : V → ℝ := fun v => ((alg.output G id (fun _ => ()) T v).2 : ℝ)
          let R0 : Finset V := Finset.univ.filter fun v => ∀ u ∈ F, v ∉ closedNbhd G u
          MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
          (∀ v, v ∉ F → 0 < cst v ∧ cst v ≤ 2 * (a : ℝ) + 1) ∧
          HasSlack
            (fun x : {x : V → ℝ // IsFeasibleOn G (Finset.univ \ F) R0 x} =>
              RoundingData.cost
                { a := (a : ℝ), C := Finset.univ \ F, R0 := R0, c := cst, x := x.1 })
            (fun x : {x : V → ℝ // IsFeasibleOn G (Finset.univ \ F) R0 x} =>
              (RoundingData.D G
                { a := (a : ℝ), C := Finset.univ \ F, R0 := R0, c := cst, x := x.1 }).card)
            (deltaA (a : ℝ)) ∧
          tauOn G (Finset.univ \ F) R0 cst ≤ (2 * (a : ℝ) + 1) * fracDom G - F.card) := by sorry

end ShortBroadcastDom.Supplement
