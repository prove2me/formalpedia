-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_quad_exists_theta
-- name    : PIW.AdelicOrbitU.quad_exists_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:30.554461+00:00
-- url     : https://prove2.me/theorems/bc1c5b1f-2311-4afd-afd2-c87d31c4638c
-- title:
--   Adelic Orbit U: quad exists theta
-- statement:
--   The Adelic Orbit U construction uses the quad exists theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L100-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L100-L127

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

theorem PIW.AdelicOrbitU.quad_exists_theta [CharZero F] (h2 : Module.finrank F E = 2)
    (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) :
    ∃ θ : E, θ ≠ 0 ∧ σ θ = -θ ∧ (∃ d : F, d ≠ 0 ∧ θ * θ = algebraMap F E d) ∧
      LinearIndependent F ![(1 : E), θ] := by sorry
