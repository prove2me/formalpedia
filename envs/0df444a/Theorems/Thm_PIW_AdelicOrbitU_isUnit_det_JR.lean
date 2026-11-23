-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_isUnit_det_JR
-- name    : PIW.AdelicOrbitU.isUnit_det_JR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:57.575808+00:00
-- url     : https://prove2.me/theorems/fc8914af-d1c5-4507-9d20-5fe26d03d0b7
-- title:
--   Adelic Orbit U: is Unit det JR
-- statement:
--   The Adelic Orbit U construction uses the is Unit det JR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/InclRAlgebraMap.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/InclRAlgebraMap.lean#L27-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem PIW.AdelicOrbitU.isUnit_det_JR (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) : IsUnit (JR (F := F) R J).det := by sorry
