-- Prove2me | Theorems.Thm_PI_WAU_Cpt_isCompact_Bx
-- name    : PI.WAU.Cpt.isCompact_Bx
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:44.171995+00:00
-- url     : https://prove2.me/theorems/11fd0036-c001-5a20-8ccf-391bc49a2955
-- title:
--   Cpt: is Compact Bx
-- statement:
--   The Cpt construction uses the is Compact Bx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/IsCompactCset.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/IsCompactCset.lean#L20-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
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

theorem PI.WAU.Cpt.isCompact_Bx (N : ℕ) : IsCompact (Bx I N) := by sorry
