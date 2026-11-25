-- Prove2me | Theorems.Thm_PI_VolStabW_OrbR_orb_orth
-- name    : PI.VolStabW.OrbR.orb_orth
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:03.321259+00:00
-- url     : https://prove2.me/theorems/0c9cf97b-f4f8-5f52-8e4f-5d03df04438a
-- title:
--   Orb R: orb orth
-- statement:
--   The Orb R construction uses the orb orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/OrbRing.lean#L100-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/OrbRing.lean#L100-L127

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

theorem PI.VolStabW.OrbR.orb_orth (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det) :
    ∀ (k : ℕ) (x y : Fin k → Fin n → S), (∀ i j, i ≠ j → hform s J (x i) (x j) = 0) →
      (∀ i j, hform s J (y i) (y j) = hform s J (x i) (x j)) →
      (∀ i, IsUnit (hform s J (x i) (x i))) →
      (∀ i (t : S), ∃ lam, lam * s lam = 1 ∧ IsUnit (hform s J (x i) (x i) - s lam * t)) →
      ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ x i = y i := by sorry
