-- Prove2me | Theorems.Thm_PI_GaugeCharW_isOpen_intSub
-- name    : PI.GaugeCharW.isOpen_intSub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:35.446907+00:00
-- url     : https://prove2.me/theorems/09b333b7-35f6-49c9-87f6-c2e54cd58abd
-- title:
--   Gauge Char W: is Open int Sub
-- statement:
--   The Gauge Char W construction uses the is Open int Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerSubgroupIntersection/IsOpenIntSub.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerSubgroupIntersection/IsOpenIntSub.lean#L27-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GaugeGap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IntInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IsOpenIntSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GaugeCharW
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable (F : Type) [Field F] [NumberField F]

theorem PI.GaugeCharW.isOpen_intSub (h3 : OpenInt) : IsOpen (intSub F : Set (AF F)) := by sorry
