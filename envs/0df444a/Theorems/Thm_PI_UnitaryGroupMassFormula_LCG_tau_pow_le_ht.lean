-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_tau_pow_le_ht
-- name    : PI.UnitaryGroupMassFormula.LCG.tau_pow_le_ht
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:40:55.805349+00:00
-- url     : https://prove2.me/theorems/e144783c-2a33-48f7-b6fd-2ad43d3551b7
-- title:
--   LCG: tau pow le ht
-- statement:
--   The LCG construction uses the tau pow le ht property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatticeIsDiscreteGroup.lean#L34-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatticeIsDiscreteGroup.lean#L34-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatticeIsDiscreteGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG

theorem PI.UnitaryGroupMassFormula.LCG.tau_pow_le_ht (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (hz : 0 < tau1 I z) (s : Sub I z) :
    tau1 I z ^ (2 * I.f * s.j) ≤ ht I s ∧ idx I s.B s.b ≠ 0 := by sorry
