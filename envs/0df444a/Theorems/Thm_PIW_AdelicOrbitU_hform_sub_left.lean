-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_hform_sub_left
-- name    : PIW.AdelicOrbitU.hform_sub_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:48:29.465114+00:00
-- url     : https://prove2.me/theorems/770e84d0-24a1-417f-8115-d87e08742826
-- title:
--   Adelic Orbit U: hform sub left
-- statement:
--   The Adelic Orbit U construction uses the hform sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L19-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Matrix Formalism.UG
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

theorem PIW.AdelicOrbitU.hform_sub_left (x y z : Fin n → S) :
    hform s J (x - y) z = hform s J x z - hform s J y z := by sorry
