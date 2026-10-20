-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_coefficientTranscendenceDegree_ge_square_of_matching
-- name    : PermanentFormulaLowerBound.matchingMarkedPermanent_coefficientTranscendenceDegree_ge_square_of_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/162e86d4-5eaa-42d5-b3fa-33dce38b67f1
-- title:
--   PermanentFormulaLowerBound.matchingMarkedPermanent_coefficientTranscendenceDegree_ge_square_of_matching
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

theorem PermanentFormulaLowerBound.matchingMarkedPermanent_coefficientTranscendenceDegree_ge_square_of_matching
    {n ell m : ℕ} (hn : n = (ell + ell) + m)
    (d : (Fin ell ⊕ Fin ell) ↪ Fin n × Fin n)
    (hrows : Function.Injective (fun y => (d y).1))
    (hcols : Function.Injective (fun y => (d y).2))
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    ((m * m : ℕ) : Cardinal) ≤
      coefficientTranscendenceDegree (matchingMarkedPermanent d) := by sorry
