-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_sum_classNum_psumExpansion_diag_8be76746319f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_sum_classNum_psumExpansion_diag_8be76746319f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:38.457061+00:00
-- url     : https://prove2.me/theorems/f4f2cf6b-5685-4de6-936e-f69a9b3170a4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient sum class Num psum Expansion diag 8be76746319f: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient sum class Num psum Expan
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient sum class Num psum Expansion diag 8be76746319f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient sum class Num psum Expansion diag 8be76746319f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L94-L98

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_sum_classNum_psumExpansion_diag_8be76746319f {N : ℕ} (x : Fin N → K → ℤ) (k : ℕ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    ∑ i, classNum (Sum.elim x x) (psumExpansion N k i) Q W =
      k * classNum x (psum (Fin N) ℤ (k - 1)) Q W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«sum_classNum_psumExpansion_diag» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_sum_classNum_psumExpansion_diag_8be76746319f
