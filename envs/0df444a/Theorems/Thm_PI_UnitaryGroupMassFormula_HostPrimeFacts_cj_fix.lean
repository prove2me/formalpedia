-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_cj_fix
-- name    : PI.UnitaryGroupMassFormula.HostPrimeFacts.cj_fix
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:15.320044+00:00
-- url     : https://prove2.me/theorems/5e8c7d02-8edb-4edc-89d8-2a24f62d35e4
-- title:
--   Host Prime Facts: cj fix
-- statement:
--   The Host Prime Facts construction uses the cj fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HostPrimeSplitting/FinrankOE.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HostPrimeSplitting/FinrankOE.lean#L14-L20

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

theorem PI.UnitaryGroupMassFormula.HostPrimeFacts.cj_fix (a : 𝓞 H.F) :
    (cj H) • (algebraMap (𝓞 H.F) (𝓞 H.E) a) = algebraMap (𝓞 H.F) (𝓞 H.E) a := by sorry
