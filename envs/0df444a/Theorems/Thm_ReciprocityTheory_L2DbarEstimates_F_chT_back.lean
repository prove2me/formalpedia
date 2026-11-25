-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_back
-- name    : ReciprocityTheory.L2DbarEstimates.F.chT_back
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:25.287175+00:00
-- url     : https://prove2.me/theorems/75f0fea0-2107-5221-813e-6da713bb73bd
-- title:
--   F: ch T back
-- statement:
--   The F construction uses the ch T back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartB.lean#L180-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartB.lean#L180-L365

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

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

theorem ReciprocityTheory.L2DbarEstimates.F.chT_back (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (G : M → V n) (D : M → ℂ) (S : M → Fin n → Fin n → ℂ)
    (hG : AEStronglyMeasurable G (vol n z)) (hD : AEStronglyMeasurable D (vol n z))
    (hS : AEStronglyMeasurable S (vol n z))
    (hGs : tsupport G ⊆ e.source) (hDs : tsupport D ⊆ e.source) (hSs : tsupport S ⊆ e.source)
    (K₀ : Set (V n)) (hK₀c : IsCompact K₀) (hK₀t : K₀ ⊆ e.target) (G' : V n → V n)
    (hG'd : ContDiff ℝ ∞ G') (hG'0 : ∀ y, y ∉ K₀ → G' y = 0) (δ : ℝ≥0∞)
    (h1 : ∫⁻ y, ‖G' y - e.target.indicator (G ∘ e.symm) y‖ₑ ^ 2 < δ)
    (h2 : ∫⁻ y, ‖(∑ j, wd n j (fun u => G' u j) y) - e.target.indicator (D ∘ e.symm) y‖ₑ ^ 2 < δ)
    (h3 : ∫⁻ y, ENNReal.ofReal (sq2 n (fun j k =>
        wdb n j (fun u => G' u k) y - wdb n k (fun u => G' u j) y -
          e.target.indicator (S ∘ e.symm) y j k)) < δ) :
    ∃ g : M → V n, IsTestForm n z g ∧ (∀ x, x ∉ e.symm '' K₀ → g x = 0) ∧
      nV n z (fun x => g x - G x) (fun _ => 0) < δ ∧
      wint n z (fun x => divF n z g x - D x) (fun _ => 0) < δ ∧
      n2 n z (fun x => sbar n z g x - S x) (fun _ => 0) < δ := by sorry
