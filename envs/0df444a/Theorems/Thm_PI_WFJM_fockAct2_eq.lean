-- Prove2me | Theorems.Thm_PI_WFJM_fockAct2_eq
-- name    : PI.WFJM.fockAct2_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:51.819514+00:00
-- url     : https://prove2.me/theorems/1a64fadb-1d35-4ecb-b620-941d65b20159
-- title:
--   WFJM: fock Act2 eq
-- statement:
--   The WFJM construction uses the fock Act2 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L38-L47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM

theorem PI.WFJM.fockAct2_eq (p q r s : ℕ) (Y : Mat r s) :
    fockAct2 p q r s Y = ∑ a : Ix p q, ∑ c : Ix r s, ∑ d : Ix r s,
      Y c d • omE (p := p) (q := q) (r := r) (s := s) (a, c) (a, d) := by sorry
