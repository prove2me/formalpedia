-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_sum_8922677a5a27
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_sum_8922677a5a27
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:05.940132+00:00
-- url     : https://prove2.me/theorems/bf375033-4d5e-4545-908c-00a26b2ce45d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num sum 8922677a5a27: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num sum 8922677a5a27
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num sum 8922677a5a27 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num sum 8922677a5a27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L44-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_sum_8922677a5a27 {σ τ : Type*} (cls : σ → K → ℤ) (s : Finset τ) (H : τ → MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (∑ t ∈ s, H t) Q W = ∑ t ∈ s, classNum cls (H t) Q W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«classNum_sum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_sum_8922677a5a27
