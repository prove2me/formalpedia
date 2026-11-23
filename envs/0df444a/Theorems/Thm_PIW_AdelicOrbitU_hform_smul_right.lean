-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_hform_smul_right
-- name    : PIW.AdelicOrbitU.hform_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:50.64101+00:00
-- url     : https://prove2.me/theorems/b52e5f46-f2c3-4d0e-b28a-7a022cc44e66
-- title:
--   Adelic Orbit U: hform smul right
-- statement:
--   The Adelic Orbit U construction uses the hform smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L31-L33

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

theorem PIW.AdelicOrbitU.hform_smul_right (a : S) (x y : Fin n → S) :
    hform s J x (a • y) = a * hform s J x y := by sorry
