-- Prove2me | Theorems.Thm_QnRdSkewW_rdV_local
-- name    : QnRdSkewW.rdV_local
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:02:35.567107+00:00
-- url     : https://prove2.me/theorems/7904fe98-1ecf-4653-bfe5-f56be175c90a
-- title:
--   Qn Rd Skew W: rd V local
-- statement:
--   The Qn Rd Skew W construction uses the rd V local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/HasDerivAtShift.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/HasDerivAtShift.lean#L51-L54

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

theorem QnRdSkewW.rdV_local (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f F : Matrix (Fin n) (Fin n) ℂ → ℂ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ G → f h = F h) (hg : g ∈ G) :
    RdV X f g = fderiv ℝ F g (g * X) := by sorry
