-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_psum_3e92c43fdb0d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_psum_3e92c43fdb0d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:08:10.639984+00:00
-- url     : https://prove2.me/theorems/e781c5ad-d8b0-43c2-ad48-f1a5f61cffe5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num psum 3e92c43fdb0d: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num psum 3e92c43fdb0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num psum 3e92c43fdb0d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num psum 3e92c43fdb0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L85-L92

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_psum_3e92c43fdb0d {N : ℕ} (x : Fin N → K → ℤ) (m : ℕ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    classNum x (psum (Fin N) ℤ m) Q W =
      ∑ i, vNumL W (classList x (Finsupp.single i m) ++ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«classNum_psum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_psum_3e92c43fdb0d
