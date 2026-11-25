-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_div
-- name    : ReciprocityTheory.L2DbarEstimates.F.chT_div
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:02:22.250968+00:00
-- url     : https://prove2.me/theorems/c001df65-4cab-5d54-9dca-84058e7c43c9
-- title:
--   F: ch T div
-- statement:
--   The F construction uses the ch T div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartB.lean#L15-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartB.lean#L15-L90

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem ReciprocityTheory.L2DbarEstimates.F.chT_div (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (G : M → V n) (D : M → ℂ) (hG : AEStronglyMeasurable G (vol n z))
    (hD : AEStronglyMeasurable D (vol n z)) (hGs : tsupport G ⊆ e.source)
    (hDs : tsupport D ⊆ e.source) (hDiv : IsWeakDiv n z G D) (ρ : V n → ℝ)
    (hρd : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρt : tsupport ρ ⊆ e.target)
    (O : Set (V n)) (hOo : IsOpen O) (h1 : ∀ y ∈ O, ρ y = 1)
    (hO : ∀ y ∈ e.target, e.symm y ∈ tsupport G ∪ tsupport D → y ∈ O)
    (φ : V n → ℂ) (hφd : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ y, ∑ j, e.target.indicator (G ∘ e.symm) y j * wd n j φ y =
      -∫ y, e.target.indicator (D ∘ e.symm) y * φ y := by sorry
