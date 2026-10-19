-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_pderiv_aeval_chain_rule
-- name    : PermanentFormulaLowerBound.pderiv_aeval_chain_rule
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/83a16269-21c3-4790-8a27-0a23ec75b8f4
-- title:
--   PermanentFormulaLowerBound.pderiv_aeval_chain_rule
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

theorem PermanentFormulaLowerBound.pderiv_aeval_chain_rule [CommSemiring F] [Fintype ι]
    (g : ι → MvPolynomial κ F) (H : MvPolynomial ι F) (j : κ) :
    MvPolynomial.pderiv j (MvPolynomial.aeval g H) =
      ∑ i : ι,
        MvPolynomial.aeval g (MvPolynomial.pderiv i H) *
          MvPolynomial.pderiv j (g i) := by sorry
