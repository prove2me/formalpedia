-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_hform_eq_dot
-- name    : PIW.AdelicOrbitU.hform_eq_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:36.047287+00:00
-- url     : https://prove2.me/theorems/bc48eec7-8014-42a7-b16c-f02dccbbe309
-- title:
--   Adelic Orbit U: hform eq dot
-- statement:
--   The Adelic Orbit U construction uses the hform eq dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L14-L17

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

theorem PIW.AdelicOrbitU.hform_eq_dot (x y : Fin n → S) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by sorry
