-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_LatticeLocalGlobalTheory_cw_perm
-- name    : PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.cw_perm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:54.592771+00:00
-- url     : https://prove2.me/theorems/8264359b-6c92-53eb-acbf-c818dfd1d461
-- title:
--   Lattice Local Global Theory: cw perm
-- statement:
--   The Lattice Local Global Theory construction uses the cw perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompactCurveEstimate.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompactCurveEstimate.lean#L38-L42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompactCurveEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CCA
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.cw_perm (cost : B.Mat k r → ℕ) {w₁ w₂ w : List (Bool × B.Mat k r)} (hp : (w₁ ++ w₂).Perm w) :
    cw cost w₁ + cw cost w₂ = cw cost w := by sorry
