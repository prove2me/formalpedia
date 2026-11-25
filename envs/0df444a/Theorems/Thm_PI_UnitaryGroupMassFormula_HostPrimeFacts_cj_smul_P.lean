-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_cj_smul_P
-- name    : PI.UnitaryGroupMassFormula.HostPrimeFacts.cj_smul_P
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:39:09.983932+00:00
-- url     : https://prove2.me/theorems/d23e0895-03f1-4514-b70f-0afd76f633ea
-- title:
--   Host Prime Facts: cj smul P
-- statement:
--   The Host Prime Facts construction uses the cj smul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HostPrimeSplitting/FinrankOE.lean#L27-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HostPrimeSplitting/FinrankOE.lean#L27-L50

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

theorem PI.UnitaryGroupMassFormula.HostPrimeFacts.cj_smul_P (P : HeightOneSpectrum (𝓞 H.E))
    (h1 : (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1) :
    (cj H) • P.asIdeal = P.asIdeal := by sorry
