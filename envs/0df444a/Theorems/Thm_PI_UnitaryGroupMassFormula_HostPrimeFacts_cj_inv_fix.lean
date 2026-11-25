-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_cj_inv_fix
-- name    : PI.UnitaryGroupMassFormula.HostPrimeFacts.cj_inv_fix
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:34.948224+00:00
-- url     : https://prove2.me/theorems/9d2346a8-17b2-5dc1-8560-cfbc570acdfc
-- title:
--   Host Prime Facts: cj inv fix
-- statement:
--   The Host Prime Facts construction uses the cj inv fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HostPrimeSplitting/FinrankOE.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HostPrimeSplitting/FinrankOE.lean#L22-L25

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

theorem PI.UnitaryGroupMassFormula.HostPrimeFacts.cj_inv_fix (a : 𝓞 H.F) :
    (cj H)⁻¹ • (algebraMap (𝓞 H.F) (𝓞 H.E) a) = algebraMap (𝓞 H.F) (𝓞 H.E) a := by sorry
