-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Capelli_pderiv_X_mul__2a5262d9a5e3
-- name    : P2M_GlobalTheory_Capelli_pderiv_X_mul__2a5262d9a5e3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:06.18519+00:00
-- url     : https://prove2.me/theorems/e3ea7b50-6ef3-4c52-bc01-289a9185c883
-- title:
--   P2 M Global Theory Capelli pderiv X mul  2a5262d9a5e3: P2 M Global Theory Capelli pderiv X mul  2a5262d9a5e3
-- statement:
--   The P2 M Global Theory Capelli pderiv X mul  2a5262d9a5e3 construction uses the P2 M Global Theory Capelli pderiv X mul  2a5262d9a5e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L19-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]

theorem P2M_GlobalTheory_Capelli_pderiv_X_mul__2a5262d9a5e3 [DecidableEq σ] (v w : σ) (Q : MvPolynomial σ K) :
    pderiv v (X w * Q) = X w * pderiv v Q + (if v = w then Q else 0) := by sorry

alias «GlobalTheory».«Capelli».«pderiv_X_mul'» := P2M_GlobalTheory_Capelli_pderiv_X_mul__2a5262d9a5e3
