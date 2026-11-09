-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_lemma_4_6
-- name    : WeightedThreeSetPacking.Main.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:28.017302+00:00
-- url     : https://prove2.me/theorems/77b7c484-775f-4713-969c-f77357379276
-- title:
--   Lemma 4.6 — All normalized identities and incidence bounds (Tong and Xu, arXiv:2610.10036v1, p. 16)
-- statement:
--   Under the standing setting of Tong and Xu, arXiv:2610.10036v1, Lemma 4.6, p. 16, use the inclusive neighborhoods, claws and exact parameters defined above. Here {v} is a final singleton.
--
--   Write $W=w_v$, $m=|C_v|$, $x=\sum_{o\in C_v}w_o/W$, $B_v=N(C_v,A)\setminus\{v\}$, $z_u=w_u/W$, $r_u=|\{o\in C_v:o\sim u\}|$, $\beta=\sum_{u\in B_v}z_u$ and $Q_v=Q(\{v\})$. For $1\le m\le3$, all four conclusions hold:
--
--   1. $$(\Delta_v+\Psi_v)/W^2=m+1-2x+\sum_{u\in B_v}(r_uz_u-(r_u-1)z_u^2).$$
--   2. $$Q_v/W\le\delta(m+\sum r_uz_u),\qquad g_v/W=\max(x-1-\beta,0).$$
--   3. Every talon has at most two secondary blockers; $\sum r_u\le2m$, $|B_v|\le2m$, and $0<z_u\le q=a^2<a$.
--   4. $$\sum z_u^2\ge S_m(x)=\max(x^2/m-1,0),\qquad0\le S_m(x)\le2mq^2.$$
--
--   This result provides the corresponding source statement in the dependency chain for the full approximation theorem.
--
--   Differences from the source:
--   - generalization: Positive rational set weights, an optimum packing O, and its rank-three conflict graph (or an analysis lift). → Positive real weights on A∪O, independent O, and finite graphs with the inherited two-sided inclusive degree bounds and maximum-neighbor assignment.; reason: These inequalities use positivity, independence and the rank-three degree bounds; every source instance and its weight-preserving lift satisfies these assumptions.
--   - encoding: Finite set families, inclusive neighborhoods, witnessed exchange multiarcs and finite sums. → Finite carrier types and Finsets, with one triple per witnessed arc and inclusive neighborhoods.; reason: This preserves common vertices, distinct-neighbor sums and incidence multiplicities.
--   - generalization: A final piece after the Arkin–Hassin reduction with the larger fixed girth required for the full decomposition. → A computed final component with graph girth greater than twice its maximum possible vertex count.; reason: A cycle or parallel-arc obstruction in a final piece would give a conflict cycle of length at most twice that count; no full root/pendant hierarchy is needed for these final pieces.
--   - generalization: The Phase I packing in the source standing setting. → Every packing satisfying the same fixed s₀-exchange square local optimality.; reason: Only the resulting local optimality, rather than the execution path of Phase I, is used.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Lemma 4.6, p. 16; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Analysis

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Lemma 4.6, p. 16. -/
theorem lemma_4_6 {V : Type} [Fintype V] [DecidableEq V] (D : Analysis V)
    (hvalid : ValidAnalysis D)
    (hparameters : FixedParameters D) (hgirth : FinalHighGirth D)
    (hlocal : SquareLocal D s₀) (v : V) (hfinal : FinalComponent D {v})
    (hm : 1 ≤ (claw D v).card ∧ (claw D v).card ≤ 3) :
    let m := (claw D v).card
    let W := D.w v
    let x := normalizedTalonMass D v
    let B := blockers D v
    let z := normalizedBlocker D v
    let r := incidence D v
    (exchangeSlack D v + separationSlack D v) / W^2 =
      (m : ℝ) + 1 - 2*x + ∑ u ∈ B, ((r u : ℝ)*z u - ((r u : ℝ)-1)*(z u)^2) ∧
    (layerCredit D {v} / W ≤ delta * ((m : ℝ) + ∑ u ∈ B, (r u : ℝ)*z u) ∧
      residual D v / W = max (x - 1 - blockerMass D v) 0) ∧
    ((∀ o ∈ claw D v, (neighbors D {o} (D.A \ {v})).card ≤ 2) ∧
      (∑ u ∈ B, r u) ≤ 2*m ∧ B.card ≤ 2*m ∧
      ∀ u ∈ B, 0 < z u ∧ z u ≤ q ∧ q = a^2 ∧ q < a) ∧
    (requiredSquareMass m x ≤ (∑ u ∈ B, (z u)^2) ∧
      0 ≤ requiredSquareMass m x ∧ requiredSquareMass m x ≤ 2*(m : ℝ)*q^2) := by sorry

end WeightedThreeSetPacking.Main
