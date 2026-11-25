-- Prove2me | Theorems.Thm_PI_WAU_Cpt_isCompact_Kset
-- name    : PI.WAU.Cpt.isCompact_Kset
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:16:54.910005+00:00
-- url     : https://prove2.me/theorems/ab7ce1c9-1661-440b-aa46-d08fe2fd545a
-- title:
--   Cpt: is Compact Kset
-- statement:
--   The Cpt construction uses the is Compact Kset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/NatSmulMulEq.lean#L168-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/NatSmulMulEq.lean#L168-L187

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_NatSmulMulEq
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
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)

theorem PI.WAU.Cpt.isCompact_Kset : IsCompact I.Kset := by sorry
