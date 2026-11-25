-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_of_equiv_0fa1882a45e0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_of_equiv_0fa1882a45e0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:35.486586+00:00
-- url     : https://prove2.me/theorems/6a43e45d-88d9-4cc1-b45b-043f8adcacc1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B norm le one iff is Integral Elem of equiv 0fa1882a45e0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Fou
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B norm le one iff is Integral Elem of equiv 0fa1882a45e0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B norm le one iff is Integral Elem of equiv 0fa1882a45e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/NormLeOneIffIsIntegralElemOfEquiv.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/NormLeOneIffIsIntegralElemOfEquiv.lean#L50-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_of_equiv_0fa1882a45e0 (p : ℕ) [Fact p.Prime] {E O K : Type*} [Field E]
    [CommRing O] [NormedField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra E K] (ι : O →+* E) (e : ℚ_[p] →+* E) (ψ : ℤ_[p] ≃+* O)
    (hψ : ∀ z, ι (ψ z) = e (algebraMap ℤ_[p] ℚ_[p] z))
    (he : algebraMap ℚ_[p] K = (algebraMap E K).comp e) (x : K) :
    ‖x‖ ≤ 1 ↔ ((algebraMap E K).comp ι).IsIntegralElem x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«norm_le_one_iff_isIntegralElem_of_equiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_of_equiv_0fa1882a45e0
