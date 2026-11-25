-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_norm_exp_le
-- name    : PI.UnitaryGroupMassFormula.LCG.BoxB.norm_exp_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:34.930647+00:00
-- url     : https://prove2.me/theorems/ccc2c664-f44c-4bd4-9c07-d9299c40c1e4
-- title:
--   Box B: norm exp le
-- statement:
--   The Box B construction uses the norm exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/BoxBound.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/BoxBound.lean#L59-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.BoxB
variable {n : ℕ}
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra Matrix.frobeniusNormedSpace

theorem PI.UnitaryGroupMassFormula.LCG.BoxB.norm_exp_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.sqrt n * Real.exp ‖X‖ := by sorry
