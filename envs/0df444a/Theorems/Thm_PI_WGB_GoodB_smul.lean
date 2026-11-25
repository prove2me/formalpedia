-- Prove2me | Theorems.Thm_PI_WGB_GoodB_smul
-- name    : PI.WGB.GoodB_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:46:11.897693+00:00
-- url     : https://prove2.me/theorems/95a2209e-cbc7-4c52-a7bf-52a11d5a41b9
-- title:
--   WGB: Good B smul
-- statement:
--   The WGB construction uses the Good B smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/DetPowUnitriB.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/DetPowUnitriB.lean#L82-L85

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
variable {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ)

theorem PI.WGB.GoodB_smul (c : ℂ) {p : MvPolynomial σ ℂ} {d : ℕ} (hp : GoodB R ψ p d) : GoodB R ψ (c • p) d := by sorry
