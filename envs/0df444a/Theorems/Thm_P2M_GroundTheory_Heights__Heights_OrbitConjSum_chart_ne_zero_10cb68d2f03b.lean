-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_chart_ne_zero_10cb68d2f03b
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_chart_ne_zero_10cb68d2f03b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:33.127612+00:00
-- url     : https://prove2.me/theorems/df377c80-c65e-515a-904b-208a41bed897
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum chart ne zero 10cb68d2f03b: P2 M Ground Theory Heights  Heights Orbit Conj Sum chart ne zero 10cb68d2f03b
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum chart ne zero 10cb68d2f03b construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum chart ne zero 10cb68d2f03b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L79-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
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
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_chart_ne_zero_10cb68d2f03b (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) (k : ι) : z ⟨k, c k⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«chart_ne_zero» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_chart_ne_zero_10cb68d2f03b
