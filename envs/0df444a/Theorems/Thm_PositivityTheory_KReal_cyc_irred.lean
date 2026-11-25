-- Prove2me | Theorems.Thm_PositivityTheory_KReal_cyc_irred
-- name    : PositivityTheory.KReal.cyc_irred
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:52.503778+00:00
-- url     : https://prove2.me/theorems/72bc0ddb-a113-471a-9200-6efb151dc963
-- title:
--   KReal: cyc irred
-- statement:
--   The KReal construction uses the cyc irred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCyc.lean#L237-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCyc.lean#L237-L356

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {r s : ℕ}

theorem PositivityTheory.KReal.cyc_irred {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] {ρ : Ix r s → Ix r s → Module.End ℂ A}
    (hadj : AdjK ρ) (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : A} (hf : HwK ρ μ f)
    (N : Submodule ℂ A) (hN : N ≤ cycK ρ f) (hK : KSt ρ N) : N = ⊥ ∨ N = cycK ρ f := by sorry
