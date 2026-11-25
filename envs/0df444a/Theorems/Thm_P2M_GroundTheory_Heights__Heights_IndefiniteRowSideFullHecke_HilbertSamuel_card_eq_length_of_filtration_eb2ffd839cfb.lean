-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_card_eq_length_of_filtration_eb2ffd839cfb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_card_eq_length_of_filtration_eb2ffd839cfb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:33.270432+00:00
-- url     : https://prove2.me/theorems/d5135053-cb09-48f0-a0e9-2fc4a26b234d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel card eq length of filtration eb2ffd839cfb: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel card eq length of filtration eb2ffd839cfb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel card eq length of filtration eb2ffd839cfb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LengthLocalizedQuotientEqZero.lean#L137-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LengthLocalizedQuotientEqZero.lean#L137-L182

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_card_eq_length_of_filtration_eb2ffd839cfb {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (x : Fin n → M) (q : Fin n → Ideal R)
    (hN0 : N 0 = ⊥) (hNl : N (Fin.last n) = ⊤)
    (hsucc : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span R {x j})
    (hprime : ∀ j, (q j).IsPrime) (hann : ∀ j (s : R), s • x j ∈ N j.castSucc ↔ s ∈ q j)
    (W : Ideal R) (hW : W ∈ (Module.annihilator R M).minimalPrimes) [W.IsPrime]
    [DecidablePred fun j => q j = W] :
    (((Finset.univ.filter fun j => q j = W).card : ℕ) : ℕ∞) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HilbertSamuel».«card_eq_length_of_filtration» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_card_eq_length_of_filtration_eb2ffd839cfb
