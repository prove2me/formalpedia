-- Prove2me | Theorems.Thm_PI_WFJM_fockAct2_Eab
-- name    : PI.WFJM.fockAct2_Eab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:55.399849+00:00
-- url     : https://prove2.me/theorems/cbe9b868-669d-4d75-8af6-3658853e0fc7
-- title:
--   WFJM: fock Act2 Eab
-- statement:
--   The WFJM construction uses the fock Act2 Eab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L143-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L143-L152

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
open MvPolynomial
open PI.FJM

theorem PI.WFJM.fockAct2_Eab (p q r s : ℕ) (c d : Ix r s) :
    fockAct2 p q r s (Eab c d) = ∑ a : Ix p q, omE (p := p) (q := q) (r := r) (s := s) (a, c) (a, d) := by sorry
