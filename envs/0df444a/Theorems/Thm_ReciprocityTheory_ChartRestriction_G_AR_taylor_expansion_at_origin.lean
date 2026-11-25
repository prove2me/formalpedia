-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_taylor_expansion_at_origin
-- name    : ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_at_origin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:36.298124+00:00
-- url     : https://prove2.me/theorems/a8d006cc-87b4-4fc4-bd04-427b27008da5
-- title:
--   AR: taylor expansion at origin
-- statement:
--   The AR construction uses the taylor expansion at origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/TaylorExpansionLocalCoordinates.lean#L46-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/TaylorExpansionLocalCoordinates.lean#L46-L88

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

theorem ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_at_origin {n a : ℕ} (G : V n → ℂ) (U : Set (V n)) (hU : IsOpen U) (h0 : (0 : V n) ∈ U)
    (hG : DifferentiableOn ℂ G U) (hO : G =O[𝓝 0] fun u => ‖u‖ ^ a) :
    ∃ b : (Fin n → ℕ) → ℂ,
      (fun u => G u - ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, u k ^ α k)
        =O[𝓝 0] fun u => ‖u‖ ^ (a + 1) := by sorry
