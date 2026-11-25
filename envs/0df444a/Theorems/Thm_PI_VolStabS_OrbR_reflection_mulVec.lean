-- Prove2me | Theorems.Thm_PI_VolStabS_OrbR_reflection_mulVec
-- name    : PI.VolStabS.OrbR.reflection_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:35.864448+00:00
-- url     : https://prove2.me/theorems/0e90f87b-c37f-4713-bde0-8a7b1cff5e70
-- title:
--   Orb R: reflection mul Vec
-- statement:
--   The Orb R construction uses the reflection mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/OrbRing.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/OrbRing.lean#L15-L25

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

theorem PI.VolStabS.OrbR.reflection_mulVec (c : S) (u v z : Fin n → S) :
    r1 s J c u v *ᵥ z = z - (c * hform s J u z) • v := by sorry
