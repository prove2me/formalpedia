-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_sigR_inclR
-- name    : PIW.AdelicOrbitU.sigR_inclR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:55.470994+00:00
-- url     : https://prove2.me/theorems/bb1462f8-cda7-42d4-b911-b1bd95f283ca
-- title:
--   Adelic Orbit U: sig R incl R
-- statement:
--   The Adelic Orbit U construction uses the sig R incl R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/InclRAlgebraMap.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/InclRAlgebraMap.lean#L16-L18

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

theorem PIW.AdelicOrbitU.sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by sorry
