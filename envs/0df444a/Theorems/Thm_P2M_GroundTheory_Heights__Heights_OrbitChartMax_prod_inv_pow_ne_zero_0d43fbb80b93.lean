-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_prod_inv_pow_ne_zero_0d43fbb80b93
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_prod_inv_pow_ne_zero_0d43fbb80b93
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:43.17637+00:00
-- url     : https://prove2.me/theorems/20320490-5996-5eff-964a-bd5475c89075
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max prod inv pow ne zero 0d43fbb80b93: P2 M Ground Theory Heights  Heights Orbit Chart Max prod inv pow ne zero 0d43fbb80b93
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max prod inv pow ne zero 0d43fbb80b93 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max prod inv pow ne zero 0d43fbb80b93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L79-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_prod_inv_pow_ne_zero_0d43fbb80b93 {Ω : Type*} [Field Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (D : ι → ℕ) : ∏ k, (z ⟨k, c k⟩)⁻¹ ^ D k ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«prod_inv_pow_ne_zero» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_prod_inv_pow_ne_zero_0d43fbb80b93
