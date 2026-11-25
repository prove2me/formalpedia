-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_psumExpansion_d622675f0759
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_psumExpansion_d622675f0759
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:03.858592+00:00
-- url     : https://prove2.me/theorems/1af66bd2-ff09-45c7-88a2-d8d52b0da47a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rename psum Expansion d622675f0759: P2 M Ground Theory Heights  Heights Numbers DVR rename psum Expansion d622675f0759
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rename psum Expansion d622675f0759 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rename psum Expansion d622675f0759 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSubQuotient.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSubQuotient.lean#L30-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_psumExpansion_d622675f0759 {M N : ℕ} (e : Fin M → Fin N) (k : ℕ) (i : Fin M) :
    rename (Sum.map e e) (psumExpansion M k i) = psumExpansion N k (e i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«rename_psumExpansion» := P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_psumExpansion_d622675f0759
