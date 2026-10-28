-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_closedProduct_stabilization
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.closedProduct_stabilization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:30:50.957585+00:00
-- url     : https://prove2.me/theorems/9110021a-4122-4344-ace3-7239c581c71b
-- title:
--   Stabilization under closed products determines the generated group
-- statement:
--   Let $F$ be a field of characteristic zero and let $K$ be its specified algebraic closure, with its embedding of $F$. All groups below are geometric subgroups of $\mathrm{GL}_n(K)$, and all closures are relative Zariski closures in that group.
--
--   Let $G_1,G_2$ be connected algebraic subgroups, and let $H=\langle G_1,G_2\rangle$ be their ordinary generated subgroup. Let $A\subseteq H$ contain the identity. If $\overline{A G_1}=A$ and $\overline{A G_2}=A$, then
--
--   $$A=H.$$
--
--   This characterizes the stable set reached by the closed-product construction.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 3, Proposition 2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

section Geometric

variable {F K : Type*} [Field F] [hchar : CharZero F] [Field K] [Algebra F K] [hclosure : IsAlgClosure F K]

variable {n : ℕ}

section

include hchar hclosure

/-- Proposition 2, PDF p.3. Both overbars cover the whole set product A Gi. -/
theorem closedProduct_stabilization (G1 G2 : Subgroup (GeometricGL n K))
    (hG1 : IsAlgebraicGroup G1) (hG2 : IsAlgebraicGroup G2)
    (hc1 : IsZariskiConnected (G1 : Set (GeometricGL n K)))
    (hc2 : IsZariskiConnected (G2 : Set (GeometricGL n K)))
    (A : Set (GeometricGL n K))
    (hA : A ⊆ (G1 ⊔ G2 : Subgroup (GeometricGL n K))) (h1 : 1 ∈ A)
    (hprod1 : zariskiClosure (A * (G1 : Set (GeometricGL n K))) = A)
    (hprod2 : zariskiClosure (A * (G2 : Set (GeometricGL n K))) = A) :
    A = (G1 ⊔ G2 : Subgroup (GeometricGL n K)) := by sorry

end

end Geometric

end QAlgorithms.Papers.Independent.Renew46.P22

end
