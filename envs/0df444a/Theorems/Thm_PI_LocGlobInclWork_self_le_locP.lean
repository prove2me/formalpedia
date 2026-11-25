-- Prove2me | Theorems.Thm_PI_LocGlobInclWork_self_le_locP
-- name    : PI.LocGlobInclWork.self_le_locP
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:33.059899+00:00
-- url     : https://prove2.me/theorems/7c2962a7-66d4-450e-9fe9-c4c6e7960568
-- title:
--   Loc Glob Incl Work: self le loc P
-- statement:
--   The Loc Glob Incl Work construction uses the self le loc P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L16-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]

theorem PI.LocGlobInclWork.self_le_locP {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    (L : Submodule (𝓞 K) W) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L := by sorry
