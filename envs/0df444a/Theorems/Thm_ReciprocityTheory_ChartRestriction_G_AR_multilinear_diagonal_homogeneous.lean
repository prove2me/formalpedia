-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_multilinear_diagonal_homogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.AR.multilinear_diagonal_homogeneous
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:01:07.321382+00:00
-- url     : https://prove2.me/theorems/ff9b5e7b-2f26-4a6a-8cdd-a5a59ccabc7f
-- title:
--   AR: multilinear diagonal homogeneous
-- statement:
--   The AR construction uses the multilinear diagonal homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/TaylorExpansionLocalCoordinates.lean#L11-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/TaylorExpansionLocalCoordinates.lean#L11-L44

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

theorem ReciprocityTheory.ChartRestriction.G.AR.multilinear_diagonal_homogeneous {n a : ℕ} (D : ContinuousMultilinearMap ℂ (fun _ : Fin a => V n) ℂ) :
    ∃ b : (Fin n → ℕ) → ℂ, ∀ u : V n,
      D (fun _ => u) = ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, u k ^ α k := by sorry
