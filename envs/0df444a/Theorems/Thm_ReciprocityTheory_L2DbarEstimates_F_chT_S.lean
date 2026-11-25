-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_S
-- name    : ReciprocityTheory.L2DbarEstimates.F.chT_S
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:34.217906+00:00
-- url     : https://prove2.me/theorems/1dda15d9-26fa-4620-982f-7e6d7adc9f16
-- title:
--   F: ch T S
-- statement:
--   The F construction uses the ch T S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartB.lean#L92-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartB.lean#L92-L171

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

theorem ReciprocityTheory.L2DbarEstimates.F.chT_S (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (G : M → V n) (S : M → Fin n → Fin n → ℂ) (hG : AEStronglyMeasurable G (vol n z))
    (hS : AEStronglyMeasurable S (vol n z)) (hGs : tsupport G ⊆ e.source)
    (hSs : tsupport S ⊆ e.source) (hSw : IsWeakS n z G S) (ρ : V n → ℝ)
    (hρd : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρt : tsupport ρ ⊆ e.target)
    (O : Set (V n)) (hOo : IsOpen O) (h1 : ∀ y ∈ O, ρ y = 1)
    (hO : ∀ y ∈ e.target, e.symm y ∈ tsupport G ∪ tsupport S → y ∈ O)
    (φ : V n → ℂ) (hφd : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (j k : Fin n) :
    ∫ y, (e.target.indicator (G ∘ e.symm) y k * wdb n j φ y -
        e.target.indicator (G ∘ e.symm) y j * wdb n k φ y) =
      -∫ y, e.target.indicator (S ∘ e.symm) y j k * φ y := by sorry
