-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_vars_c54e0d859ef5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_vars_c54e0d859ef5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:05.182532+00:00
-- url     : https://prove2.me/theorems/e8219acf-5885-4423-8c2e-f54094419d67
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class Num rename vars c54e0d859ef5: P2 M Ground Theory Heights  Heights Numbers DVR class Num rename vars c54e0d859ef5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class Num rename vars c54e0d859ef5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class Num rename vars c54e0d859ef5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L89-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_vars_c54e0d859ef5 {σ τ : Type*} [DecidableEq σ] [DecidableEq τ] (cls : τ → K → ℤ) (φ : σ → τ) (H : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename φ H) Q W = classNum (cls ∘ φ) H Q W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classNum_rename_vars» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_vars_c54e0d859ef5
