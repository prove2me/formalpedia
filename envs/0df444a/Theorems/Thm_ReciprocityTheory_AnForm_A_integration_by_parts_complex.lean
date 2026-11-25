-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integration_by_parts_complex
-- name    : ReciprocityTheory.AnForm.A.integration_by_parts_complex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:24.900612+00:00
-- url     : https://prove2.me/theorems/fc5cc727-6e25-5902-992e-e18999641060
-- title:
--   A: integration by parts complex
-- statement:
--   The A construction uses the integration by parts complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L48-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L48-L151

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.A.integration_by_parts_complex {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (a b : (Fin (n + 1) → ℂ) → ℝ)
    (U K : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (ha : ContDiffOn ℝ 3 a U) (hb : ContDiffOn ℝ 3 b U) (hφ : ∀ i, ContDiffOn ℝ 3 (φ i) U)
    (h0 : ∀ y ∉ K, ∀ j k, (fun y => cplx a y * dzb k (cplx b) y) =ᶠ[𝓝 y] (fun _ => 0) ∧
      dz j (cplx a) y * dzb k (cplx b) y = 0 ∧ cplx a y * dz j (dzb k (cplx b)) y = 0) :
    Integrable (fun y => ∑ j, ∑ k, dz j (cplx a) y * dzb k (cplx b) y * hessCof φ y j k) ∧
    Integrable (fun y => cplx a y * ∑ j, ∑ k, hessCof φ y j k * dz j (dzb k (cplx b)) y) ∧
    (∫ y, ∑ j, ∑ k, dz j (cplx a) y * dzb k (cplx b) y * hessCof φ y j k) +
      (∫ y, cplx a y * ∑ j, ∑ k, hessCof φ y j k * dz j (dzb k (cplx b)) y) = 0 := by sorry
