-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_quad_sigma_sigma
-- name    : PIW.AdelicOrbitU.quad_sigma_sigma
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:48:06.54315+00:00
-- url     : https://prove2.me/theorems/ca19f2eb-b0b4-49d2-8cd3-8fb5a0c9ebb0
-- title:
--   Adelic Orbit U: quad sigma sigma
-- statement:
--   The Adelic Orbit U construction uses the quad sigma sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L74-L80

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

theorem PIW.AdelicOrbitU.quad_sigma_sigma (h2 : Module.finrank F E = 2)
    (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) (a : E) : σ (σ a) = a := by sorry
