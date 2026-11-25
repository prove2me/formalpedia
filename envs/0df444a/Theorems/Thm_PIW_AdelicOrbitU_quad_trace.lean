-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_quad_trace
-- name    : PIW.AdelicOrbitU.quad_trace
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:48:03.379694+00:00
-- url     : https://prove2.me/theorems/8e0d08bb-eeb8-4678-a7bf-a0e4a4583dea
-- title:
--   Adelic Orbit U: quad trace
-- statement:
--   The Adelic Orbit U construction uses the quad trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L203-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L203-L213

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
variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
  (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ])
  (R : Type) [CommRing R] [Algebra F R]
include h2 hli

theorem PIW.AdelicOrbitU.quad_trace {d : F} (hd : θ * θ = algebraMap F E d) (a b : R) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) = 2 * a := by sorry
