-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_cyclicMatchingBlock_snd_injective
-- name    : PermanentFormulaLowerBound.cyclicMatchingBlock_snd_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/426e5539-9565-44e9-8648-4a319e9bd434
-- title:
--   PermanentFormulaLowerBound.cyclicMatchingBlock_snd_injective
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

theorem PermanentFormulaLowerBound.cyclicMatchingBlock_snd_injective {n k : ℕ}
    (hk : 0 < k) (t : Fin n) (j : Fin (n / k)) :
    Function.Injective
      (fun x : ↥(cyclicMatchingBlock hk t j) => x.1.2) := by sorry
