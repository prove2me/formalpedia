-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_hs_exp_le
-- name    : PI.UnitaryGroupMassFormula.LCG.BoxB.hs_exp_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:49:21.169365+00:00
-- url     : https://prove2.me/theorems/f087e164-571c-5615-bb2d-5c2e5193eed1
-- title:
--   Box B: hs exp le
-- statement:
--   The Box B construction uses the hs exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/BoxBound.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/BoxBound.lean#L66-L72

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

theorem PI.UnitaryGroupMassFormula.LCG.BoxB.hs_exp_le (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (NormedSpace.exp X) ≤ (Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2 := by sorry
