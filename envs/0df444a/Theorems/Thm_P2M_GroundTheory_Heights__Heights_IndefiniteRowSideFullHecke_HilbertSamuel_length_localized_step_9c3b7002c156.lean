-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_step_9c3b7002c156
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_step_9c3b7002c156
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:10.193803+00:00
-- url     : https://prove2.me/theorems/6897ef04-9329-4b6f-babc-07c9efa488bc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel length localized step 9c3b7002c156: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel length localized step 9c3b7002c156 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel length localized step 9c3b7002c156 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LengthLocalizedQuotientEqZero.lean#L97-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LengthLocalizedQuotientEqZero.lean#L97-L135

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_step_9c3b7002c156 (p : Ideal R) [p.IsPrime] {M : Type*} [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (x : M) (q : Ideal R) (hB : B = A ⊔ Submodule.span R {x})
    (hq : ∀ s : R, s • x ∈ A ↔ s ∈ q) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (M ⧸ A)) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ q)) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (M ⧸ B)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HilbertSamuel».«length_localized_step» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_step_9c3b7002c156
