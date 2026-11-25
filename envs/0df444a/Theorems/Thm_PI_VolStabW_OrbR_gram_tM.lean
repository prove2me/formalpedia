-- Prove2me | Theorems.Thm_PI_VolStabW_OrbR_gram_tM
-- name    : PI.VolStabW.OrbR.gram_tM
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:38.973303+00:00
-- url     : https://prove2.me/theorems/d6b2fe98-f296-4ec5-83ad-3292d9cbe9fa
-- title:
--   Orb R: gram t M
-- statement:
--   The Orb R construction uses the gram t M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/OrbRing.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/OrbRing.lean#L131-L135

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

theorem PI.VolStabW.OrbR.gram_tM {m : ℕ} (X : Fin m → Fin n → S) (i j : Fin m) :
    hform s J (X i) (X j) = (cT s (tM X) * J * tM X) i j := by sorry
