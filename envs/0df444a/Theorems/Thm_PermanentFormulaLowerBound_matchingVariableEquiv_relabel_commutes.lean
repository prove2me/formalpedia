-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingVariableEquiv_relabel_commutes
-- name    : PermanentFormulaLowerBound.matchingVariableEquiv_relabel_commutes
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/80e6efc9-56a6-4c14-b3e2-cca4ad81d8f5
-- title:
--   PermanentFormulaLowerBound.matchingVariableEquiv_relabel_commutes
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

theorem PermanentFormulaLowerBound.matchingVariableEquiv_relabel_commutes
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (e : Equiv.Perm (Fin n × Fin n))
    (he : ∀ y : Y, e (d₀ y) = d y) :
    (matchingVariableEquiv d₀).symm.trans
      (Equiv.sumCongr (Equiv.refl Y)
        (matchingOutsideRelabelEquiv d₀ d e he)) =
      e.trans (matchingVariableEquiv d).symm := by sorry
