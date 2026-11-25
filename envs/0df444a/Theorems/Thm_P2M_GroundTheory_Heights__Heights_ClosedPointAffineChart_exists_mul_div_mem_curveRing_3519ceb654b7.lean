-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_exists_mul_div_mem_curveRing_3519ceb654b7
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_exists_mul_div_mem_curveRing_3519ceb654b7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:38.130326+00:00
-- url     : https://prove2.me/theorems/389d7723-4980-4fac-8e01-3fa7e461f9e8
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Affine Chart exists mul div mem curve Ring 3519ceb654b7: P2 M Ground Theory Heights  Heights Closed Point Affine Chart exists mul div mem curve Ring 35
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Affine Chart exists mul div mem curve Ring 3519ceb654b7 construction uses the P2 M Ground Theory Heights  Heights Closed Point Affine Chart exists mul div mem curve Ring 3519ceb654b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L89-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L89-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointAffineChart
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

theorem P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_exists_mul_div_mem_curveRing_3519ceb654b7 {m : Ideal (curveRing y)} (hm : m.IsMaximal) {e : ℕ} {g : K'}
    (hg0 : g ≠ 0) (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    {h : K'} (hh : ∀ t : T, y ⟨(), t⟩ ≠ 0 → h / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t)) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (h / g) ∈ curveRing y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointAffineChart».«exists_mul_div_mem_curveRing» := P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_exists_mul_div_mem_curveRing_3519ceb654b7
