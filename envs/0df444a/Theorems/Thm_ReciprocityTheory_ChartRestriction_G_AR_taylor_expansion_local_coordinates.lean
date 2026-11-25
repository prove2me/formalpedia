-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_taylor_expansion_local_coordinates
-- name    : ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_local_coordinates
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:03.326941+00:00
-- url     : https://prove2.me/theorems/6a4f3c5e-209e-4c50-9ad7-ac53a629f723
-- title:
--   AR: taylor expansion local coordinates
-- statement:
--   The AR construction uses the taylor expansion local coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/TaylorExpansionLocalCoordinates.lean#L90-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/TaylorExpansionLocalCoordinates.lean#L90-L133

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR
open Filter Topology Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_local_coordinates {n a : ℕ} (g : V n → ℂ) (ζ : V n → V n) (U : Set (V n)) (x : V n)
    (hU : IsOpen U) (hx : x ∈ U) (hg : DifferentiableOn ℂ g U) (hζ : DifferentiableOn ℂ ζ U)
    (hζ0 : ζ x = 0) (hdet : (fderiv ℂ ζ x).det ≠ 0) (hO : g =O[𝓝 x] fun v => ‖v - x‖ ^ a) :
    ∃ b : (Fin n → ℕ) → ℂ,
      (fun v => g v - ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, ζ v k ^ α k)
        =O[𝓝 x] fun v => ‖v - x‖ ^ (a + 1) := by sorry
