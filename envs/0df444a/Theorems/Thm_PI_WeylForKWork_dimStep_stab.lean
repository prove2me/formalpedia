-- Prove2me | Theorems.Thm_PI_WeylForKWork_dimStep_stab
-- name    : PI.WeylForKWork.dimStep_stab
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:59.929443+00:00
-- url     : https://prove2.me/theorems/061a7ea7-e63d-5e6a-bdc1-649b23b50db7
-- title:
--   Weyl For KWork: dim Step stab
-- statement:
--   The Weyl For KWork construction uses the dim Step stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/DimStep.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/DimStep.lean#L30-L33

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

theorem PI.WeylForKWork.dimStep_stab {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H} :
    IsKStableOn (allPos n) σ W ↔ Stab (fun g : Kset (allPos n) => σ g.1) W := by sorry
