-- Prove2me | Theorems.Thm_QnRdSkewW_hasDerivAt_shift
-- name    : QnRdSkewW.hasDerivAt_shift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:05:04.273354+00:00
-- url     : https://prove2.me/theorems/c06749b7-1516-59ce-88e4-67179a99a785
-- title:
--   Qn Rd Skew W: has Deriv At shift
-- statement:
--   The Qn Rd Skew W construction uses the has Deriv At shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/HasDerivAtShift.lean#L63-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/HasDerivAtShift.lean#L63-L79

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

theorem QnRdSkewW.hasDerivAt_shift (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X)))
      (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) t := by sorry
