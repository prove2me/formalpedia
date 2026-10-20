-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_of_nonempty
-- name    : PermanentFormulaLowerBound.matchingPolynomial_of_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/7cfc27b8-e8f7-4183-8725-7b7224be495c
-- title:
--   PermanentFormulaLowerBound.matchingPolynomial_of_nonempty
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

theorem PermanentFormulaLowerBound.matchingPolynomial_of_nonempty {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell))
    (hP : P.Nonempty) :
    matchingPolynomial p P =
      Polynomial.C (matchingInjectionSum p P) -
        ∑ u : ↥P,
          (Polynomial.X : Polynomial F) ^ (2 ^ (u.1 : ℕ)) *
            matchingPolynomial p (P.erase u.1) := by sorry
