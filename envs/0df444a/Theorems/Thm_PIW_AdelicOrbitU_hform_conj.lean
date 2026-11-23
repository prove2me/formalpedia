-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_hform_conj
-- name    : PIW.AdelicOrbitU.hform_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:09.937195+00:00
-- url     : https://prove2.me/theorems/11bf3da1-f137-43c0-bb89-08d49667993e
-- title:
--   Adelic Orbit U: hform conj
-- statement:
--   The Adelic Orbit U construction uses the hform conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean#L35-L45

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

theorem PIW.AdelicOrbitU.hform_conj (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (x y : Fin n → S) :
    s (hform s J x y) = hform s J y x := by sorry
