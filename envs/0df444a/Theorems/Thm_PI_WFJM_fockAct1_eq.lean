-- Prove2me | Theorems.Thm_PI_WFJM_fockAct1_eq
-- name    : PI.WFJM.fockAct1_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:23.390347+00:00
-- url     : https://prove2.me/theorems/109d2b4c-e464-423c-b4ee-4598b34190ef
-- title:
--   WFJM: fock Act1 eq
-- statement:
--   The WFJM construction uses the fock Act1 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L21-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L21-L32

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

theorem PI.WFJM.fockAct1_eq (p q r s : ℕ) (Z : Mat p q) :
    fockAct1 p q r s Z = ∑ a : Ix p q, ∑ b : Ix p q, ∑ c : Ix r s,
      Z a b • omE (p := p) (q := q) (r := r) (s := s) (a, c) (b, c) := by sorry
