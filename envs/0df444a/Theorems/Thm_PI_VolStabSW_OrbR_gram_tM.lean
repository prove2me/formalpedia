-- Prove2me | Theorems.Thm_PI_VolStabSW_OrbR_gram_tM
-- name    : PI.VolStabSW.OrbR.gram_tM
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:04.892379+00:00
-- url     : https://prove2.me/theorems/c97e1aaa-3a5e-4f0f-88e9-58faae5838f0
-- title:
--   Orb R: gram t M
-- statement:
--   The Orb R construction uses the gram t M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/OrbRing.lean#L165-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/OrbRing.lean#L165-L169

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

theorem PI.VolStabSW.OrbR.gram_tM {m : ℕ} (X : Fin m → Fin n → S) (i j : Fin m) :
    hform s J (X i) (X j) = (cT s (tM X) * J * tM X) i j := by sorry
