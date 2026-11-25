-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_mcMap_rename_midVar_8ade0d3b342f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_mcMap_rename_midVar_8ade0d3b342f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:10:35.85203+00:00
-- url     : https://prove2.me/theorems/c9e01326-b816-4353-ac17-3b97b1daff33
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right mc Map rename mid Var 8ade0d3b342f: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right mc Map renam
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right mc Map rename mid Var 8ade0d3b342f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right mc Map rename mid Var 8ade0d3b342f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L30-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivRight
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_mcMap_rename_midVar_8ade0d3b342f (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    mcMap R (joinCoord x (joinCoord w z)) (rename (midVar ι₂) h) =
      rename (Sum.map id Sum.inr) (mcMap R (joinCoord x z) h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorRight».«mcMap_rename_midVar» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_mcMap_rename_midVar_8ade0d3b342f
