-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classList_diag_22aec79530dc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classList_diag_22aec79530dc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:09:15.820141+00:00
-- url     : https://prove2.me/theorems/e89c65ee-6de3-4ef8-8701-c73896cff69c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class List diag 22aec79530dc: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class List diag 22aec79530dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class List diag 22aec79530dc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class List diag 22aec79530dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L61-L66

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classList_diag_22aec79530dc {N : ℕ} (x : Fin N → K → ℤ) (i : Fin N) (j l : ℕ) :
    classList (Sum.elim x x) (Finsupp.single (Sum.inl i) j + Finsupp.single (Sum.inr i) l) =
      classList x (Finsupp.single i (j + l)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«classList_diag» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classList_diag_22aec79530dc
