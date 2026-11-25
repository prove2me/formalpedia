-- Prove2me | Theorems.Thm_PI_WAU_Cpt_ctsA_fst
-- name    : PI.WAU.Cpt.ctsA_fst
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:44:14.906899+00:00
-- url     : https://prove2.me/theorems/2798e071-4c58-43e2-8a84-b93ef48adf25
-- title:
--   Cpt: cts A fst
-- statement:
--   The Cpt construction uses the cts A fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/IsCompactCset.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/IsCompactCset.lean#L30-L31

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

theorem PI.WAU.Cpt.ctsA_fst (i j : Fin I.n) : CtsA (bs I) (fun p : Co I × Co I => matOf I p.1 i j) := by sorry
