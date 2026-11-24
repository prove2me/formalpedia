-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_monomial_eq_0ee7393f4501
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_monomial_eq_0ee7393f4501
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:56.120308+00:00
-- url     : https://prove2.me/theorems/9d3067c9-6cbb-418a-9483-c5a461a6705f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class Num monomial eq 0ee7393f4501: P2 M Ground Theory Heights  Heights Numbers DVR class Num monomial eq 0ee7393f4501
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class Num monomial eq 0ee7393f4501 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class Num monomial eq 0ee7393f4501 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L75-L80

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_monomial_eq_0ee7393f4501 {σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) (c : ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    classNum cls (monomial μ c) Q W = c * vNumL W (classList cls μ ++ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classNum_monomial_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_monomial_eq_0ee7393f4501
