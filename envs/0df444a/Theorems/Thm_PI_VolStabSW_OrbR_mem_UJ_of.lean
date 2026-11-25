-- Prove2me | Theorems.Thm_PI_VolStabSW_OrbR_mem_UJ_of
-- name    : PI.VolStabSW.OrbR.mem_UJ_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:06.244024+00:00
-- url     : https://prove2.me/theorems/f12d22a9-ae7e-57bc-a54e-757b9c9660f3
-- title:
--   Orb R: mem UJ of
-- statement:
--   The Orb R construction uses the mem UJ of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/OrbRing.lean#L58-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/OrbRing.lean#L58-L78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_OrbRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

theorem PI.VolStabSW.OrbR.mem_UJ_of (hdet : IsUnit J.det) (T : Matrix (Fin n) (Fin n) S)
    (key : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) = T := by sorry
