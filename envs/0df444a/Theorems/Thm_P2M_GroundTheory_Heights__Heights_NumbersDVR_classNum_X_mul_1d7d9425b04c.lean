-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_X_mul_1d7d9425b04c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_X_mul_1d7d9425b04c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:06.811422+00:00
-- url     : https://prove2.me/theorems/178af37a-211c-5ac8-98bd-9039f51245b0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class Num X mul 1d7d9425b04c: P2 M Ground Theory Heights  Heights Numbers DVR class Num X mul 1d7d9425b04c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class Num X mul 1d7d9425b04c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class Num X mul 1d7d9425b04c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L251-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L251-L263

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
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
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_X_mul_1d7d9425b04c {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (s : σ) (H : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (X s * H) Q W =
      ∑ μ ∈ H.support, H.coeff μ * vNumL W (cls s :: (classList cls μ ++ Q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classNum_X_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_X_mul_1d7d9425b04c
