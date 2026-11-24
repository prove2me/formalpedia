-- Prove2me | Theorems.Thm_PI_LocGlobInclWork_mem_of_local
-- name    : PI.LocGlobInclWork.mem_of_local
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:51.154634+00:00
-- url     : https://prove2.me/theorems/95bdd810-30a8-4d65-8a65-ee3f3abdb3a4
-- title:
--   Loc Glob Incl Work: mem of local
-- statement:
--   The Loc Glob Incl Work construction uses the mem of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L24-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L24-L39

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

theorem PI.LocGlobInclWork.mem_of_local {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (N : Submodule (𝓞 K) W) (x : W)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ N) : x ∈ N := by sorry
