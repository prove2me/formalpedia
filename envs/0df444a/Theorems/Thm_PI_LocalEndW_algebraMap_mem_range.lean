-- Prove2me | Theorems.Thm_PI_LocalEndW_algebraMap_mem_range
-- name    : PI.LocalEndW.algebraMap_mem_range
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:06.039825+00:00
-- url     : https://prove2.me/theorems/e4b21dd0-49e1-4800-b423-8acc366a9f9b
-- title:
--   Local End W: algebra Map mem range
-- statement:
--   The Local End W construction uses the algebra Map mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/AlgebraMapMemRange.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/AlgebraMapMemRange.lean#L12-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IsUniformInducingOfVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_AlgebraMapMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open PI PI.LocalEndW

theorem PI.LocalEndW.algebraMap_mem_range {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (τ : v.adicCompletion F →+* v.adicCompletion F) (a : F) :
    algebraMap F (v.adicCompletion F) a ∈ Set.range τ := by sorry
