-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_mem
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.theta_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:05.964932+00:00
-- url     : https://prove2.me/theorems/ccfa976c-2b5b-4826-9493-fd1d520a6a71
-- title:
--   Unit Det Root: theta mem
-- statement:
--   The Unit Det Root construction uses the theta mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/DetMemOfEntries.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/DetMemOfEntries.lean#L15-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.theta_mem (b : ℤ) (d : ℕ) : UnitDetRootDefs.cmTheta b d ∈ KF b d := by sorry
