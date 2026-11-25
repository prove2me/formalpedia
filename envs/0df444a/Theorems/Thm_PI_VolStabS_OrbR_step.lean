-- Prove2me | Theorems.Thm_PI_VolStabS_OrbR_step
-- name    : PI.VolStabS.OrbR.step
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:56.077798+00:00
-- url     : https://prove2.me/theorems/3a094979-f99e-59b0-8cdb-7c320a06df33
-- title:
--   Orb R: step
-- statement:
--   The Orb R construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/OrbRing.lean#L66-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/OrbRing.lean#L66-L148

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_OrbRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

theorem PI.VolStabS.OrbR.step (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det)
    (a b : Fin n → S) (hab : hform s J b b = hform s J a a) (hu : IsUnit (hform s J a a))
    (lam : S) (hlam : lam * s lam = 1) (hc : IsUnit (hform s J a a - s lam * hform s J b a)) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) *ᵥ a = b ∧
      ∀ z, hform s J a z = 0 → hform s J b z = 0 → (g : Matrix (Fin n) (Fin n) S) *ᵥ z = z := by sorry
