-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_uc_fin
-- name    : PIW.AdelicOrbitU.uc_fin
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:48:43.360915+00:00
-- url     : https://prove2.me/theorems/3deb0458-29bd-46e9-ae98-60164f08d89a
-- title:
--   Adelic Orbit U: uc fin
-- statement:
--   The Adelic Orbit U construction uses the uc fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/LocalSum.lean#L173-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/LocalSum.lean#L173-L177

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped RestrictedProduct

theorem PIW.AdelicOrbitU.uc_fin (F : Type) [Field F] [NumberField F] :
    UnitChoice (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) := by sorry
