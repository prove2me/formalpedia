-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_quad_exists_not_mem
-- name    : PIW.AdelicOrbitU.quad_exists_not_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:10.608817+00:00
-- url     : https://prove2.me/theorems/769fdb32-6b39-5d40-9e75-a835cc6af2d3
-- title:
--   Adelic Orbit U: quad exists not mem
-- statement:
--   The Adelic Orbit U construction uses the quad exists not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L15-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
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
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem PIW.AdelicOrbitU.quad_exists_not_mem (h2 : Module.finrank F E = 2) :
    ∃ a : E, a ∉ (algebraMap F E).range := by sorry
