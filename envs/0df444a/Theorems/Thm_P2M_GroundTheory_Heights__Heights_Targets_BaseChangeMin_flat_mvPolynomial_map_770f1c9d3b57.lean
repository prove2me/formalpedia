-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_flat_mvPolynomial_map_770f1c9d3b57
-- name    : P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_flat_mvPolynomial_map_770f1c9d3b57
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:04.327037+00:00
-- url     : https://prove2.me/theorems/b69b9693-46f8-4116-be83-2f57e9be2502
-- title:
--   P2 M Ground Theory Heights  Heights Targets Base Change Min flat mv Polynomial map 770f1c9d3b57: P2 M Ground Theory Heights  Heights Targets Base Change Min flat mv Polynomial map 770f1c9d3b57
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Base Change Min flat mv Polynomial map 770f1c9d3b57 construction uses the P2 M Ground Theory Heights  Heights Targets Base Change Min flat mv Polynomial map 770f1c9d3b57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L20-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
attribute [local instance] MvPolynomial.algebraMvPolynomial
omit [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_flat_mvPolynomial_map_770f1c9d3b57 :
    Module.Flat (MvPolynomial σ F) (MvPolynomial σ F') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«BaseChangeMin».«flat_mvPolynomial_map» := P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_flat_mvPolynomial_map_770f1c9d3b57
