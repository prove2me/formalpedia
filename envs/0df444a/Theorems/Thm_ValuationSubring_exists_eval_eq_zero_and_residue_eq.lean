-- Prove2me | Theorems.Thm_ValuationSubring_exists_eval_eq_zero_and_residue_eq
-- name    : ValuationSubring.exists_eval_eq_zero_and_residue_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/c9ecfb77-f1cb-5f0f-8a07-0dd4c3239466
-- title:
--   Roots lift along the residue map of a valuation subring
-- statement:
--   Let $L$ be an algebraically closed field and let $A$ be a valuation subring of $L$, a local ring with residue map $\operatorname{res}_A \colon A \to \kappa_A$ onto its residue field. Let $q \in A[X]$ be a polynomial whose leading coefficient is a unit of $A$, and let $a_0 \in \kappa_A$ be a root of the reduction $\bar q \in \kappa_A[X]$, that is, of the image of $q$ under the coefficientwise map induced by $\operatorname{res}_A$. The assertion is that there exists $\alpha \in A$ with $q(\alpha) = 0$ and $\operatorname{res}_A(\alpha) = a_0$; thus every residual root lifts to a genuine root of $q$ in $A$ reducing to it. No Henselian or separability hypothesis is imposed, and the root produced is an exact root of $q$ in $A$, not merely an approximate one.
--
--   This is the root-lifting device for valuation rings of an algebraically closed field: a root of the reduction of a polynomial with unit leading coefficient is the reduction of an honest root in the valuation ring. It is used in the construction of liftings of characteristic-$p$ data to characteristic zero, being cited by [`ModularCurve.inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed`](thm.html#ModularCurve.inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed) and by [`WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom`](thm.html#WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_eval_eq_zero_and_residue_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_eval_eq_zero_and_residue_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (q : Polynomial A) (hq : IsUnit q.leadingCoeff)
    (a₀ : IsLocalRing.ResidueField A)
    (hroot : (q.map (IsLocalRing.residue A)).eval a₀ = 0) :
    ∃ α : A, q.eval α = 0 ∧ IsLocalRing.residue A α = a₀ := by sorry
