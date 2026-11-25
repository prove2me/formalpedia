-- Prove2me | Theorems.Thm_PI_WAU_maximal_compact_isCompact
-- name    : PI.WAU.maximal_compact_isCompact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:32:37.046408+00:00
-- url     : https://prove2.me/theorems/153238fe-d768-474b-ab93-7c4059747d5d
-- title:
--   WAU: maximal compact is Compact
-- statement:
--   The WAU construction uses the maximal compact is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionA.lean#L64-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionA.lean#L64-L64

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_NatSmulMulEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct Matrix

theorem PI.WAU.maximal_compact_isCompact : KCompact := by sorry
