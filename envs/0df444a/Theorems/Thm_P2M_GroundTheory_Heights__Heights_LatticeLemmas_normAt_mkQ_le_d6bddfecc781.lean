-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_normAt_mkQ_le_d6bddfecc781
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_normAt_mkQ_le_d6bddfecc781
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:23.309944+00:00
-- url     : https://prove2.me/theorems/f12dcb30-f5d7-4035-a463-554c87fe36e0
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas norm At mk Q le d6bddfecc781: P2 M Ground Theory Heights  Heights Lattice Lemmas norm At mk Q le d6bddfecc781
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas norm At mk Q le d6bddfecc781 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas norm At mk Q le d6bddfecc781 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMeanQuotient.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMeanQuotient.lean#L15-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMeanQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField GroundTheory.Heights₂.Heights Submodule Cardinal TensorProduct
universe u v w
noncomputable section
variable {K : Type u} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_normAt_mkQ_le_d6bddfecc781 (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    (hF : M.Saturated F) (σ : K →+* ℂ) (e : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ e) ≤ M.normAt σ e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«normAt_mkQ_le» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_normAt_mkQ_le_d6bddfecc781
