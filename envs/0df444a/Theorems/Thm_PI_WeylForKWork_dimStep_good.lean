-- Prove2me | Theorems.Thm_PI_WeylForKWork_dimStep_good
-- name    : PI.WeylForKWork.dimStep_good
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:22.65777+00:00
-- url     : https://prove2.me/theorems/f4d2ad03-c1be-4927-91a7-eb0e178de3db
-- title:
--   Weyl For KWork: dim Step good
-- statement:
--   The Weyl For KWork construction uses the dim Step good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/DimStep.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/DimStep.lean#L12-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix DimensionInduction

theorem PI.WeylForKWork.dimStep_good {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (Kset (allPos n)) σ) :
    Good (fun g : Kset (allPos n) => σ g.1) := by sorry
