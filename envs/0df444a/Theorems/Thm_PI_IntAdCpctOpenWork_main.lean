-- Prove2me | Theorems.Thm_PI_IntAdCpctOpenWork_main
-- name    : PI.IntAdCpctOpenWork.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:33.586137+00:00
-- url     : https://prove2.me/theorems/415ee1ea-40bc-4357-a6ca-af29d33d9f4d
-- title:
--   Int Ad Cpct Open Work: main
-- statement:
--   The Int Ad Cpct Open Work construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicIntegersCompact/IsCompactAdicCompletionIntegers.lean#L154-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicIntegersCompact/IsCompactAdicCompletionIntegers.lean#L154-L162

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_IntAdelesCompactOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.IntAdCpctOpenWork
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.IntAdCpctOpenWork.main : Formalism.L2.Props.IntAdelesCompactOpen := by sorry
