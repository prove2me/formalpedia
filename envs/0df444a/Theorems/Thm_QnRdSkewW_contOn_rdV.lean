-- Prove2me | Theorems.Thm_QnRdSkewW_contOn_rdV
-- name    : QnRdSkewW.contOn_rdV
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:44.581073+00:00
-- url     : https://prove2.me/theorems/8e00b0c6-f04c-40c2-8a6c-ccea17a49cc8
-- title:
--   Qn Rd Skew W: cont On rd V
-- statement:
--   The Qn Rd Skew W construction uses the cont On rd V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/HasDerivAtShift.lean#L89-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/HasDerivAtShift.lean#L89-L99

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_HasDerivAtShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}

theorem QnRdSkewW.contOn_rdV (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) : ContinuousOn (RdV X f) G := by sorry
