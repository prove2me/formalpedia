-- Prove2me | Theorems.Thm_PI_WFJM_fockAct1_Eab
-- name    : PI.WFJM.fockAct1_Eab
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:58.285618+00:00
-- url     : https://prove2.me/theorems/1c6c5782-01a8-4d73-a693-8b22576e9422
-- title:
--   WFJM: fock Act1 Eab
-- statement:
--   The WFJM construction uses the fock Act1 Eab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L134-L141

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

theorem PI.WFJM.fockAct1_Eab (p q r s : ℕ) (a b : Ix p q) :
    fockAct1 p q r s (Eab a b) = ∑ c : Ix r s, omE (p := p) (q := q) (r := r) (s := s) (a, c) (b, c) := by sorry
