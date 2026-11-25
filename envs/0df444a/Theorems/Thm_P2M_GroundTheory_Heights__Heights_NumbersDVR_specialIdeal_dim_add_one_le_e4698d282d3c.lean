-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_specialIdeal_dim_add_one_le_e4698d282d3c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_specialIdeal_dim_add_one_le_e4698d282d3c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:50.413693+00:00
-- url     : https://prove2.me/theorems/ec852d5e-cfd3-51d7-9aa5-271decd8e5e7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR special Ideal dim add one le e4698d282d3c: P2 M Ground Theory Heights  Heights Numbers DVR special Ideal dim add one le e4698d282d3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR special Ideal dim add one le e4698d282d3c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR special Ideal dim add one le e4698d282d3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagProjSpecialDim.lean#L20-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagProjSpecialDim.lean#L20-L50

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_specialIdeal_dim_add_one_le_e4698d282d3c {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} {ι : K → Type*} (P : Ideal (MvPolynomial (Σ k, ι k) O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) = ⊥) :
    ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
        P.map (MvPolynomial.map (IsLocalRing.residue O))) + 1 ≤
      ringKrullDim (MvPolynomial (Σ k, ι k) O ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«specialIdeal_dim_add_one_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_specialIdeal_dim_add_one_le_e4698d282d3c
