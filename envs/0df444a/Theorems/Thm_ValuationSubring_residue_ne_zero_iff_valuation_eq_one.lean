-- Prove2me | Theorems.Thm_ValuationSubring_residue_ne_zero_iff_valuation_eq_one
-- name    : ValuationSubring.residue_ne_zero_iff_valuation_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/794b64f3-a28c-5ff0-965d-9b4a29203ead
-- title:
--   Nonzero residue iff valuation one in a valuation subring
-- statement:
--   Let $K$ be a field and let $A$ be a valuation subring of $K$, with its canonical valuation $A.\mathrm{valuation}$ taking values in the associated value group and with $A$ a local ring, so that the residue map `IsLocalRing.residue` from $A$ to its residue field is available. Let $a$ be an element of $K$ together with a proof $ha$ that $a$ lies in $A$, so that $\langle a, ha\rangle$ denotes the corresponding element of the subring $A$. The theorem asserts the equivalence of two conditions: the residue of $\langle a, ha\rangle$ in the residue field of $A$ is nonzero, and the value $A.\mathrm{valuation}\,a$ of the valuation of $A$ at $a$ equals $1$. Thus an element of $A$ has nonzero image in the residue field exactly when it has valuation $1$, i.e. exactly when it is a unit of $A$.
--
--   This is the standard identification, for a valuation ring, of the complement of the maximal ideal with the elements of valuation $1$ (the units). It is used for unit/non-unit bookkeeping with coordinates and similar quantities at a place, and is cited by [`FreyPackage.frey_exists_decomposition_branch_swap_of_a_mod_eight`](thm.html#FreyPackage.frey_exists_decomposition_branch_swap_of_a_mod_eight) and by [`TWLoc.frobenius_conj_mul_pow_inv_wild`](thm.html#TWLoc.frobenius_conj_mul_pow_inv_wild).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_residue_ne_zero_iff_valuation_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.residue_ne_zero_iff_valuation_eq_one {K : Type*} [Field K]
    (A : ValuationSubring K) {a : K} (ha : a ∈ A) :
    IsLocalRing.residue A ⟨a, ha⟩ ≠ 0 ↔ A.valuation a = 1 := by sorry
