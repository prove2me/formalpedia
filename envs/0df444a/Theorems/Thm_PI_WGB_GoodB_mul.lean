-- Prove2me | Theorems.Thm_PI_WGB_GoodB_mul
-- name    : PI.WGB.GoodB_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:35.182357+00:00
-- url     : https://prove2.me/theorems/ce2cc659-98a4-4883-9b4c-0199c40e45ce
-- title:
--   WGB: Good B mul
-- statement:
--   The WGB construction uses the Good B mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/DetPowUnitriB.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/DetPowUnitriB.lean#L48-L62

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

theorem PI.WGB.GoodB_mul {p q : MvPolynomial σ ℂ} {d d' : ℕ} (hp : GoodB R ψ p d) (hq : GoodB R ψ q d') :
    GoodB R ψ (p * q) (d + d') := by sorry
