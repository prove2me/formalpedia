-- Prove2me | Theorems.Thm_P2M_PermanentFormulaLowerBound_pderiv_bind__chain_rule_ab7619a8c457
-- name    : P2M_PermanentFormulaLowerBound_pderiv_bind__chain_rule_ab7619a8c457
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/a0331f6a-be57-4241-adc3-1a101b73d245
-- title:
--   P2M_PermanentFormulaLowerBound_pderiv_bind__chain_rule_ab7619a8c457
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
variable {ι : Type u} {κ : Type v} {F : Type w}

theorem P2M_PermanentFormulaLowerBound_pderiv_bind__chain_rule_ab7619a8c457 [CommSemiring F] [Fintype ι]
    (g : ι → MvPolynomial κ F) (H : MvPolynomial ι F) (j : κ) :
    MvPolynomial.pderiv j (MvPolynomial.bind₁ g H) =
      ∑ i : ι,
        MvPolynomial.bind₁ g (MvPolynomial.pderiv i H) *
          MvPolynomial.pderiv j (g i) := by sorry

alias «PermanentFormulaLowerBound».«pderiv_bind₁_chain_rule» := P2M_PermanentFormulaLowerBound_pderiv_bind__chain_rule_ab7619a8c457
