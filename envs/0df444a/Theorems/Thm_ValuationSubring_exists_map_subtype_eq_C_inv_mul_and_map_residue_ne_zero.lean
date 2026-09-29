-- Prove2me | Theorems.Thm_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
-- name    : ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/470f4834-010e-52e7-a48d-89b555d9bf71
-- title:
--   Gauss normalisation of a polynomial over a valuation subring
-- statement:
--   Let $L$ be a field and let $A$ be a valuation subring of $L$ (so $A$ is a local ring, with residue map `IsLocalRing.residue A` onto its residue field). Let $q_1 \in L[X]$ be a polynomial with $q_1 \neq 0$. The assertion is that there exist a polynomial $q \in A[X]$ and a scalar $c \in L$ such that: $c \neq 0$; the image of $q$ under the coefficientwise map induced by the inclusion $A \hookrightarrow L$ (that is, `A.subtype`) equals $C(c^{-1}) \cdot q_1$, the polynomial $q_1$ scaled by the constant $c^{-1}$; and the image of $q$ under the coefficientwise reduction `IsLocalRing.residue A` is a nonzero polynomial over the residue field of $A$. Thus every nonzero polynomial over $L$ becomes, after multiplication by a single nonzero scalar of $L$, a polynomial with coefficients in $A$ at least one of whose coefficients is a unit of $A$, i.e. a polynomial whose reduction modulo the maximal ideal of $A$ does not vanish.
--
--   This is the normalisation of a polynomial by its Gauss content with respect to a valuation subring: dividing by a coefficient of extremal valuation makes the polynomial integral and primitive, so that its reduction to the residue field is nonzero. It is used in the analysis of integrality of points on modular curves with respect to a Gauss valuation subring, via [`ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem`](thm.html#ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem) and the criteria [`ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_j_eq_of_liesOverPrime_xHTop`](thm.html#ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_j_eq_of_liesOverPrime_xHTop) and [`ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime`](thm.html#ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    (q₁ : Polynomial L) (hq₁ : q₁ ≠ 0) :
    ∃ q : Polynomial A, ∃ c : L, c ≠ 0 ∧
      (q.map A.subtype = Polynomial.C c⁻¹ * q₁) ∧ q.map (IsLocalRing.residue A) ≠ 0 := by sorry
