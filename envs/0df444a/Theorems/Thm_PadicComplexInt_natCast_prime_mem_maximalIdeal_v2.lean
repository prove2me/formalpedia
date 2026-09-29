-- Prove2me | Theorems.Thm_PadicComplexInt_natCast_prime_mem_maximalIdeal_v2
-- name    : PadicComplexInt.natCast_prime_mem_maximalIdeal_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T11:41:13.986215+00:00
-- url     : https://prove2.me/theorems/8fd9a5b3-c34b-470e-9f4c-45ed3d02c9dc
-- title:
--   The rational prime lies in the maximal ideal of the C_p integers
-- statement:
--   The rational prime p belongs to the maximal ideal of the valuation ring of C_p.
-- source:
--   Standard p-adic valuation theory.

import Definitions.Def_KN_SeededThetaConstructionV2B
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

set_option autoImplicit false
noncomputable section

/-- The rational prime `p` lies in the maximal ideal of the valuation ring of
`ℂ_p`. -/
theorem PadicComplexInt.natCast_prime_mem_maximalIdeal_v2
    (p : ℕ) [Fact p.Prime] :
    (p : 𝓞_ℂ_[p]) ∈ IsLocalRing.maximalIdeal (𝓞_ℂ_[p]) := by sorry
