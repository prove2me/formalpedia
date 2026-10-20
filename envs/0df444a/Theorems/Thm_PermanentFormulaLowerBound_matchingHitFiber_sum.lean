-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingHitFiber_sum
-- name    : PermanentFormulaLowerBound.matchingHitFiber_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/c8283acb-4463-4db7-b7f3-23a0df36133a
-- title:
--   PermanentFormulaLowerBound.matchingHitFiber_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

theorem PermanentFormulaLowerBound.matchingHitFiber_sum {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) {P : Finset (Fin ell)}
    (u : ↥P) (b : Fin m) :
    (∑ rho : {rho : ↥P ↪ Fin m // rho u = b},
      ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
        p b ^ (2 ^ (u.1 : ℕ)) *
          matchingAvoidingInjectionSum p (P.erase u.1) b := by sorry
