-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_WeightedDegree_weightedHomogeneousComponent_map_2963633f44fc
-- name    : P2M_GroundTheory_Heights__Heights_WeightedDegree_weightedHomogeneousComponent_map_2963633f44fc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:24.487829+00:00
-- url     : https://prove2.me/theorems/86180ebb-15cf-44b8-8f6f-9d8430014a98
-- title:
--   P2 M Ground Theory Heights  Heights Weighted Degree weighted Homogeneous Component map 2963633f44fc: P2 M Ground Theory Heights  Heights Weighted Degree weighted Homogeneous Component map 2963633f44fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Weighted Degree weighted Homogeneous Component map 2963633f44fc construction uses the P2 M Ground Theory Heights  Heights Weighted Degree weighted Homogeneous Component map 2963633f44fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L44-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConservationOfNumberLE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightedHomogeneousComponentMap
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

theorem P2M_GroundTheory_Heights__Heights_WeightedDegree_weightedHomogeneousComponent_map_2963633f44fc [DecidableEq K] (b : K → ℕ) (y : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) b (map (algebraMap R R') y) =
      map (algebraMap R R') (weightedHomogeneousComponent (blockWeight ι) b y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«WeightedDegree».«weightedHomogeneousComponent_map» := P2M_GroundTheory_Heights__Heights_WeightedDegree_weightedHomogeneousComponent_map_2963633f44fc
