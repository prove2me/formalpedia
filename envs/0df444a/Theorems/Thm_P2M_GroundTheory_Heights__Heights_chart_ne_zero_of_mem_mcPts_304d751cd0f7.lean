-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chart_ne_zero_of_mem_mcPts_304d751cd0f7
-- name    : P2M_GroundTheory_Heights__Heights_chart_ne_zero_of_mem_mcPts_304d751cd0f7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:23.059284+00:00
-- url     : https://prove2.me/theorems/9eafe477-82cf-4674-ac67-c39ccd1687c4
-- title:
--   P2 M Ground Theory Heights  Heights chart ne zero of mem mc Pts 304d751cd0f7: P2 M Ground Theory Heights  Heights chart ne zero of mem mc Pts 304d751cd0f7
-- statement:
--   The P2 M Ground Theory Heights  Heights chart ne zero of mem mc Pts 304d751cd0f7 construction uses the P2 M Ground Theory Heights  Heights chart ne zero of mem mc Pts 304d751cd0f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L91-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegreeRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι]
variable [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_chart_ne_zero_of_mem_mcPts_304d751cd0f7 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) (k : ι) : z ⟨k, c k⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chart_ne_zero_of_mem_mcPts» := P2M_GroundTheory_Heights__Heights_chart_ne_zero_of_mem_mcPts_304d751cd0f7
