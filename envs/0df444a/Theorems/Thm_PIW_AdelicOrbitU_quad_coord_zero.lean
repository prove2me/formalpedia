-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_quad_coord_zero
-- name    : PIW.AdelicOrbitU.quad_coord_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:49:40.054921+00:00
-- url     : https://prove2.me/theorems/d1525cc3-fe17-45ad-8796-67e67e3fdf09
-- title:
--   Adelic Orbit U: quad coord zero
-- statement:
--   The Adelic Orbit U construction uses the quad coord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L171-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L171-L173

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

theorem PIW.AdelicOrbitU.quad_coord_zero (a b : R) : (quadBasisR h2 hli R).repr (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) 0 = a := by sorry
