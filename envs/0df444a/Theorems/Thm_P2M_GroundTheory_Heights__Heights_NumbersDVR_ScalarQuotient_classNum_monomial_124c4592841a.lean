-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_monomial_124c4592841a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_monomial_124c4592841a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:04.635928+00:00
-- url     : https://prove2.me/theorems/7a457ba2-cf56-4048-881c-88a2f8d42af1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num monomial 124c4592841a: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num monomial 124c4592841a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num monomial 124c4592841a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num monomial 124c4592841a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L49-L57

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_monomial_124c4592841a {σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) (c : ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (monomial μ c) Q W = c * vNumL W (classList cls μ ++ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«classNum_monomial» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_monomial_124c4592841a
