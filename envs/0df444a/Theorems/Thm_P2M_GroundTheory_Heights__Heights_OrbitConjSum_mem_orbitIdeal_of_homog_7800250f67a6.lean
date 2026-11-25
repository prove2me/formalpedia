-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_mem_orbitIdeal_of_homog_7800250f67a6
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_mem_orbitIdeal_of_homog_7800250f67a6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:16.18415+00:00
-- url     : https://prove2.me/theorems/997edd0c-f17b-45ad-bb10-b9e704ba739e
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum mem orbit Ideal of homog 7800250f67a6: P2 M Ground Theory Heights  Heights Orbit Conj Sum mem orbit Ideal of homog 7800250f67a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum mem orbit Ideal of homog 7800250f67a6 construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum mem orbit Ideal of homog 7800250f67a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L41-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L41-L62

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

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_mem_orbitIdeal_of_homog_7800250f67a6 (x : Cone n (AlgebraicClosure ℚ)) {f : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f d) (h0 : aeval (flatCone x) f = 0) :
    f ∈ orbitIdeal x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«mem_orbitIdeal_of_homog» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_mem_orbitIdeal_of_homog_7800250f67a6
