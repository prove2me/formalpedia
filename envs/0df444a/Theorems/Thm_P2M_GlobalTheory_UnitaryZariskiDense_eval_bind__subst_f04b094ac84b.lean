-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitaryZariskiDense_eval_bind__subst_f04b094ac84b
-- name    : P2M_GlobalTheory_UnitaryZariskiDense_eval_bind__subst_f04b094ac84b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:18.799799+00:00
-- url     : https://prove2.me/theorems/d2f22163-825b-43c5-908f-3dd456fbef0d
-- title:
--   P2 M Global Theory Unitary Zariski Dense eval bind  subst f04b094ac84b: P2 M Global Theory Unitary Zariski Dense eval bind  subst f04b094ac84b
-- statement:
--   The P2 M Global Theory Unitary Zariski Dense eval bind  subst f04b094ac84b construction uses the P2 M Global Theory Unitary Zariski Dense eval bind  subst f04b094ac84b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense

theorem P2M_GlobalTheory_UnitaryZariskiDense_eval_bind__subst_f04b094ac84b {σ τ : Type} (y : τ → ℂ) (f : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ) :
    eval y (bind₁ f p) = eval (fun v => eval y (f v)) p := by sorry

alias «GlobalTheory».«UnitaryZariskiDense».«eval_bind₁_subst» := P2M_GlobalTheory_UnitaryZariskiDense_eval_bind__subst_f04b094ac84b
