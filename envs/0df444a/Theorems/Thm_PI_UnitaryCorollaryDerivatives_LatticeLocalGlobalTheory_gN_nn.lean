-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_LatticeLocalGlobalTheory_gN_nn
-- name    : PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.gN_nn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:47:42.930165+00:00
-- url     : https://prove2.me/theorems/c897bcbd-7a98-43b6-96c1-b84aa020adea
-- title:
--   Lattice Local Global Theory: g N nn
-- statement:
--   The Lattice Local Global Theory construction uses the g N nn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompactCurveEstimate.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompactCurveEstimate.lean#L52-L56

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

theorem PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.gN_nn (g : B.Mat k r) : 0 ≤ gN g := by sorry
