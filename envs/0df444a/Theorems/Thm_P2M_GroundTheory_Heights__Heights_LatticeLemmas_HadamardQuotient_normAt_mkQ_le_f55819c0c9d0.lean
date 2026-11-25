-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_normAt_mkQ_le_f55819c0c9d0
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_normAt_mkQ_le_f55819c0c9d0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:07.804064+00:00
-- url     : https://prove2.me/theorems/9fe015b4-25b1-423c-9623-265c0024bc84
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Hadamard Quotient norm At mk Q le f55819c0c9d0: P2 M Ground Theory Heights  Heights Lattice Lemmas Hadamard Quotient norm At mk Q le f55819c0c9d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Hadamard Quotient norm At mk Q le f55819c0c9d0 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Hadamard Quotient norm At mk Q le f55819c0c9d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardQuotient.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardQuotient.lean#L78-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardQuotient
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Module Submodule
open GroundTheory.Heights₂.Heights
universe u v w
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLemmas.HadamardQuotient
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_normAt_mkQ_le_f55819c0c9d0 (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
    (σ : K →+* ℂ) (x : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ x) ≤ M.normAt σ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«HadamardQuotient».«normAt_mkQ_le» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_normAt_mkQ_le_f55819c0c9d0
