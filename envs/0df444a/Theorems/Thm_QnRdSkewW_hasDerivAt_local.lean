-- Prove2me | Theorems.Thm_QnRdSkewW_hasDerivAt_local
-- name    : QnRdSkewW.hasDerivAt_local
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:51:45.615813+00:00
-- url     : https://prove2.me/theorems/914fea53-c204-43a5-946d-a3f1fb584612
-- title:
--   Qn Rd Skew W: has Deriv At local
-- statement:
--   The Qn Rd Skew W construction uses the has Deriv At local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/HasDerivAtShift.lean#L30-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/HasDerivAtShift.lean#L30-L49

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

theorem QnRdSkewW.hasDerivAt_local (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f F : Matrix (Fin n) (Fin n) ℂ → ℂ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ G → f h = F h) (hg : g ∈ G) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by sorry
