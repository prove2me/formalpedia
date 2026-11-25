-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_hform_single
-- name    : PIW.AdelicOrbitU.hform_single
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:43.746455+00:00
-- url     : https://prove2.me/theorems/a86d0bb8-8d91-4738-af76-a8f7f0681632
-- title:
--   Adelic Orbit U: hform single
-- statement:
--   The Adelic Orbit U construction uses the hform single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L47-L56

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

theorem PIW.AdelicOrbitU.hform_single (i j : Fin n) :
    hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by sorry
