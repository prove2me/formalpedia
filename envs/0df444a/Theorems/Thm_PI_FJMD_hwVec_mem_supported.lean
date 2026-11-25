-- Prove2me | Theorems.Thm_PI_FJMD_hwVec_mem_supported
-- name    : PI.FJMD.hwVec_mem_supported
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:36.972941+00:00
-- url     : https://prove2.me/theorems/0f6c6449-8526-4d0c-9bdd-83a41da7d782
-- title:
--   FJMD: hw Vec mem supported
-- statement:
--   The FJMD construction uses the hw Vec mem supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L134-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L134-L166

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
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
open PI PI.FJMD
open PI.FJM

theorem PI.FJMD.hwVec_mem_supported (p q r s : ℕ) (a b c d : List ℤ) :
    hwVec p q r s a b c d ∈ MvPolynomial.supported ℂ
      {l : Ln p q r s | inS a.length b.length c.length d.length l} := by sorry
