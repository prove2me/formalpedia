-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_quotient_eq_zero_506f8fa2ab32
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_quotient_eq_zero_506f8fa2ab32
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:26.726247+00:00
-- url     : https://prove2.me/theorems/8932ac3c-bd0d-58b0-a02a-5daff2f525e8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel length localized quotient eq zero 506f8fa2ab32: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hil
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel length localized quotient eq zero 506f8fa2ab32 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel length localized quotient eq zero 506f8fa2ab32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LengthLocalizedQuotientEqZero.lean#L50-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LengthLocalizedQuotientEqZero.lean#L50-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_quotient_eq_zero_506f8fa2ab32 (p q : Ideal R) [p.IsPrime] (h : ¬ q ≤ p) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ q)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HilbertSamuel».«length_localized_quotient_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_quotient_eq_zero_506f8fa2ab32
