-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_bitOutcome_sign
-- name    : QEC.Coding.CSSGibbs.bitOutcome_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:01.406178+00:00
-- url     : https://prove2.me/theorems/d1b67f4f-e2ef-4507-9976-463af3117168
-- title:
--   CSSGibbs: bit Outcome sign
-- statement:
--   The CSSGibbs construction uses the bit Outcome sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L168-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L168-L172

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem QEC.Coding.CSSGibbs.bitOutcome_sign (b : ZMod 2) :
    (bitOutcome b).sign = binaryPhaseScalar b := by sorry
