-- Prove2me | Theorems.Thm_PI_LocGlobInclWork_exists_unit_at
-- name    : PI.LocGlobInclWork.exists_unit_at
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:05.606879+00:00
-- url     : https://prove2.me/theorems/9f3cb0a7-ff48-4de9-9702-4ea7c6a49290
-- title:
--   Loc Glob Incl Work: exists unit at
-- statement:
--   The Loc Glob Incl Work construction uses the exists unit at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L76-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L76-L95

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

theorem PI.LocGlobInclWork.exists_unit_at (w : HeightOneSpectrum (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hw : w ∉ S) (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ t : 𝓞 K, t ∉ w.asIdeal ∧
      algebraMap (𝓞 K) K t ∈ ∏ v ∈ S, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n v := by sorry
