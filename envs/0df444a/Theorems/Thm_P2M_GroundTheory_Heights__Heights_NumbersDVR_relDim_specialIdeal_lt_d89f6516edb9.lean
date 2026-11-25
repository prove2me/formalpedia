-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_specialIdeal_lt_d89f6516edb9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_specialIdeal_lt_d89f6516edb9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:23.884798+00:00
-- url     : https://prove2.me/theorems/c9266386-b9a0-44c1-905e-d507c042ad86
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rel Dim special Ideal lt d89f6516edb9: P2 M Ground Theory Heights  Heights Numbers DVR rel Dim special Ideal lt d89f6516edb9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rel Dim special Ideal lt d89f6516edb9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rel Dim special Ideal lt d89f6516edb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagProjSpecialDim.lean#L52-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagProjSpecialDim.lean#L52-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagProjSpecialDim
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_specialIdeal_lt_d89f6516edb9 {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} (P : Ideal (MRing ι O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MRing ι O) = ⊥) (n : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim (specialIdeal P) < ((n : ℕ) : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«relDim_specialIdeal_lt» := P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_specialIdeal_lt_d89f6516edb9
