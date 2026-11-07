-- Prove2me | Theorems.Thm_VDCyclePack_lemma_5_1
-- name    : VDCyclePack.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:34.189749+00:00
-- url     : https://prove2.me/theorems/49a20681-fa0e-4e32-a1bf-31fb86c55479
-- title:
--   Lemma 5.1: $W_R\le 16\,\mathbb E[\beta(U)]$ for the sample including each $C\in R$ with probability $x_C/2$
-- statement:
--   Let $R$ be a finite family of cycles of a finite graph $G$ with positive weights $x_C$ whose loads are at most one at every vertex (for instance any $R\subseteq S$ in Theorem 4.2). Let $Q$ be obtained by including each $C\in R$ independently with probability $x_C/2$, and let $U=\bigcup_{C\in Q}C$. Then
--   $$
--   W_R\ \le\ 16\,\mathbb E\bigl[\beta(U)\bigr],\qquad W_R=\sum_{\{C,C'\}\subseteq R,\ C\neq C',\ V(C)\cap V(C')\neq\emptyset}x_Cx_{C'} .
--   $$
--
--   This charging lemma bounds the weight of intersecting pairs by the expected cycle rank of a random union, which the structural hypothesis of Theorem 4.2 controls.
--
--   **Formalization Note** The expectation is the finite sum over the subsets of $R$ with the product law.
--
--   Differences from the source:
--   - generalization: R ⊆ S, with S, x as in Theorem 4.2 → any finite family R with WeightedFamily R x (cycles, x C > 0, loads ≤ 1); reason: every R ⊆ S has these properties, and the lemma uses no other property of S
--   - encoding: Q random, E[β(U)] → sampleExp R x (fun Q => cycleRank (Q.sup id)), the sum over Q ⊆ R of the product-law probability times β; reason: the expectation of a function of Q is the sum over its finite law
--   - encoding: W_R, a sum over unordered pairs → WR R x = (1/2) · the sum over ordered pairs of distinct intersecting members; reason: same value
--   - encoding: β(U) → cycleRank of the union in the subgraph lattice; reason: the paper's definitions (pp.9–10)
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 5.1, p.15

import Mathlib
import Definitions.Def_VDCyclePack_WeightedFamily
import Definitions.Def_VDCyclePack_WR
import Definitions.Def_VDCyclePack_sampleExp
import Definitions.Def_VDCyclePack_cycleRank

namespace VDCyclePack

/-- **Lemma 5.1 (charging intersecting pairs to branch vertices).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 5.1, p.15: "Let R ⊆ S, and let Q be obtained by including each C ∈ R
independently with probability x_C/2. If U = ⋃_{C∈Q} C, then W_R ≤ 16 E[β(U)]."

Let `R` be a finite family of cycles of `G` with positive weights `x` and loads at most one. If the
random subfamily `Q ⊆ R` contains each `C ∈ R` independently with probability `x C / 2`, then
`W_R ≤ 16·E[β(⋃_{C∈Q} C)]`.

**Formalization Note.** The paper's `R ⊆ S` is used only through the properties of `S` (cycles,
positive weights, loads at most one), which `WeightedFamily R x` states for `R` directly. The
expectation is the finite sum `sampleExp` over the product law on subsets of `R`. -/
theorem lemma_5_1 {V : Type*} [Fintype V] (G : SimpleGraph V) (R : Finset G.Subgraph)
    (x : G.Subgraph → ℝ) (hR : WeightedFamily R x) :
    WR R x ≤ 16 * sampleExp R x (fun Q => (cycleRank (Q.sup id) : ℝ)) := by sorry

end VDCyclePack
