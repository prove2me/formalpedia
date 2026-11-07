-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_syndromeOutcome_apply
-- name    : QEC.Coding.CSSGibbs.syndromeOutcome_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:35.993834+00:00
-- url     : https://prove2.me/theorems/fb403cfe-1aae-4f6b-b6ee-9cce46f826d5
-- title:
--   CSSGibbs: syndrome Outcome apply
-- statement:
--   The CSSGibbs construction uses the syndrome Outcome apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L165-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L165-L166

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

theorem QEC.Coding.CSSGibbs.syndromeOutcome_apply (s : κ → ZMod 2) (j : κ) :
    syndromeOutcome κ s j = bitOutcome (s j) := by sorry

attribute [defeq] QEC.Coding.CSSGibbs.syndromeOutcome_apply
