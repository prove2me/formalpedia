-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_quad_coord_one
-- name    : PIW.AdelicOrbitU.quad_coord_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:47:52.132312+00:00
-- url     : https://prove2.me/theorems/e860deb0-dca6-4e81-943e-a607764b8a23
-- title:
--   Adelic Orbit U: quad coord one
-- statement:
--   The Adelic Orbit U construction uses the quad coord one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L175-L177

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

theorem PIW.AdelicOrbitU.quad_coord_one (a b : R) : (quadBasisR h2 hli R).repr (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) 1 = b := by sorry
