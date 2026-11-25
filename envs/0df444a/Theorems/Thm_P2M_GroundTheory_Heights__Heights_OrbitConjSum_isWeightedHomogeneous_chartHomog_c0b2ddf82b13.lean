-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_isWeightedHomogeneous_chartHomog_c0b2ddf82b13
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_isWeightedHomogeneous_chartHomog_c0b2ddf82b13
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:59.030014+00:00
-- url     : https://prove2.me/theorems/dfc47915-5af4-40cf-ad13-e9a7dff9a17f
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum is Weighted Homogeneous chart Homog c0b2ddf82b13: P2 M Ground Theory Heights  Heights Orbit Conj Sum is Weighted Homogeneous chart Homog c0b2ddf82b13
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum is Weighted Homogeneous chart Homog c0b2ddf82b13 construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum is Weighted Homogeneous chart Homog c0b2ddf82b13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L123-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L123-L132

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

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_isWeightedHomogeneous_chartHomog_c0b2ddf82b13 (c : (k : ι) → Fin (n k + 1))
    (P : MvPolynomial (Coord n) ℤ) :
    IsWeightedHomogeneous (coordDeg n) (chartHomog c P) (fun _ ↦ P.totalDegree) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«isWeightedHomogeneous_chartHomog» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_isWeightedHomogeneous_chartHomog_c0b2ddf82b13
