-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_ef_le_two
-- name    : PI.UnitaryGroupMassFormula.HostPrimeFacts.ef_le_two
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:39:24.537418+00:00
-- url     : https://prove2.me/theorems/3b34280a-746a-4d03-8aad-49719c511f71
-- title:
--   Host Prime Facts: ef le two
-- statement:
--   The Host Prime Facts construction uses the ef le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HostPrimeSplitting/FinrankOE.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HostPrimeSplitting/FinrankOE.lean#L57-L70

import Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open scoped Pointwise
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HostPrimeFacts
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

theorem PI.UnitaryGroupMassFormula.HostPrimeFacts.ef_le_two (P : HeightOneSpectrum (𝓞 H.E)) :
    P.asIdeal.ramificationIdx (𝓞 H.F) * P.asIdeal.inertiaDeg (𝓞 H.F) ≤ 2 := by sorry
