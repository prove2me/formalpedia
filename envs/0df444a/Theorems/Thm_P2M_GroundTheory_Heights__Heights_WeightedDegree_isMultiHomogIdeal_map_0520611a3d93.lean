-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_WeightedDegree_isMultiHomogIdeal_map_0520611a3d93
-- name    : P2M_GroundTheory_Heights__Heights_WeightedDegree_isMultiHomogIdeal_map_0520611a3d93
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:57.326259+00:00
-- url     : https://prove2.me/theorems/30a141a9-b85a-5b84-9d65-27de95d39df9
-- title:
--   P2 M Ground Theory Heights  Heights Weighted Degree is Multi Homog Ideal map 0520611a3d93: P2 M Ground Theory Heights  Heights Weighted Degree is Multi Homog Ideal map 0520611a3d93
-- statement:
--   The P2 M Ground Theory Heights  Heights Weighted Degree is Multi Homog Ideal map 0520611a3d93 construction uses the P2 M Ground Theory Heights  Heights Weighted Degree is Multi Homog Ideal map 0520611a3d93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L54-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L54-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConservationOfNumberLE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightedHomogeneousComponentMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_map_e1ed5f7bf88c

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
open MvPolynomial NumbersDVR
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.WeightedDegree
variable {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (M₀ : Submonoid R) [IsLocalization M₀ R']
include M₀

theorem P2M_GroundTheory_Heights__Heights_WeightedDegree_isMultiHomogIdeal_map_0520611a3d93 [DecidableEq K] {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    IsMultiHomogIdeal (I.map (algebraMap (MRing ι R) (MRing ι R'))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«WeightedDegree».«isMultiHomogIdeal_map» := P2M_GroundTheory_Heights__Heights_WeightedDegree_isMultiHomogIdeal_map_0520611a3d93
