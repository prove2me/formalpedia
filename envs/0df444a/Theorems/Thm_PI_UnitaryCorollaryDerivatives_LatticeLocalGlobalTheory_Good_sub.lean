-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_LatticeLocalGlobalTheory_Good_sub
-- name    : PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.Good.sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:21:16.280929+00:00
-- url     : https://prove2.me/theorems/a1dc701d-4f27-4fbe-a694-f6d03f1b0a6d
-- title:
--   Good: sub
-- statement:
--   The Good construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompactCurveEstimate.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompactCurveEstimate.lean#L25-L34

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

theorem PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.Good.sub {n : ℕ} {w w' : List (Bool × B.Mat k r)} (h : Good k r n w) (hs : w'.Sublist w) :
    Good k r n w' := by sorry
