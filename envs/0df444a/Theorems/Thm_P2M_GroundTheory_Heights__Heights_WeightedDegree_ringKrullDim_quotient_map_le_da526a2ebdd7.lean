-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_WeightedDegree_ringKrullDim_quotient_map_le_da526a2ebdd7
-- name    : P2M_GroundTheory_Heights__Heights_WeightedDegree_ringKrullDim_quotient_map_le_da526a2ebdd7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:14.560175+00:00
-- url     : https://prove2.me/theorems/f52642ae-ccb4-4f60-a928-cf24eb379cb9
-- title:
--   P2 M Ground Theory Heights  Heights Weighted Degree ring Krull Dim quotient map le da526a2ebdd7: P2 M Ground Theory Heights  Heights Weighted Degree ring Krull Dim quotient map le da526a2ebdd7
-- statement:
--   The P2 M Ground Theory Heights  Heights Weighted Degree ring Krull Dim quotient map le da526a2ebdd7 construction uses the P2 M Ground Theory Heights  Heights Weighted Degree ring Krull Dim quotient map le da526a2ebdd7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L26-L42

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
include M₀

theorem P2M_GroundTheory_Heights__Heights_WeightedDegree_ringKrullDim_quotient_map_le_da526a2ebdd7 (I : Ideal (MRing ι R)) :
    ringKrullDim (MRing ι R' ⧸ I.map (algebraMap (MRing ι R) (MRing ι R'))) ≤
      ringKrullDim (MRing ι R ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«WeightedDegree».«ringKrullDim_quotient_map_le» := P2M_GroundTheory_Heights__Heights_WeightedDegree_ringKrullDim_quotient_map_le_da526a2ebdd7
