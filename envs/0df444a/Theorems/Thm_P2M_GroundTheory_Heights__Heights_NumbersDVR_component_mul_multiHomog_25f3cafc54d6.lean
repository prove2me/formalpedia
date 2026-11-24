-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_multiHomog_25f3cafc54d6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_multiHomog_25f3cafc54d6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:41.9138+00:00
-- url     : https://prove2.me/theorems/2cd7986d-b5ad-45a0-a81f-385dda4e3c11
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR component mul multi Homog 25f3cafc54d6: P2 M Ground Theory Heights  Heights Numbers DVR component mul multi Homog 25f3cafc54d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR component mul multi Homog 25f3cafc54d6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR component mul multi Homog 25f3cafc54d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PColonMultiHomog.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PColonMultiHomog.lean#L9-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_multiHomog_25f3cafc54d6 {R : Type*} [CommRing R] {K : Type} [DecidableEq K]
    {ι : K → Type} (y f : MRing ι R) (b s : K → ℕ) (hf : IsMultiHomog f s) :
    weightedHomogeneousComponent (blockWeight ι) b y * f =
      weightedHomogeneousComponent (blockWeight ι) (b + s) (y * f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«component_mul_multiHomog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_multiHomog_25f3cafc54d6
