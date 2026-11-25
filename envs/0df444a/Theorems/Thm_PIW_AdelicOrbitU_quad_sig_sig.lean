-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_quad_sig_sig
-- name    : PIW.AdelicOrbitU.quad_sig_sig
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:47:56.241828+00:00
-- url     : https://prove2.me/theorems/5e6463f9-714d-4da2-955a-6859822fae3e
-- title:
--   Adelic Orbit U: quad sig sig
-- statement:
--   The Adelic Orbit U construction uses the quad sig sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L215-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L215-L219

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

theorem PIW.AdelicOrbitU.quad_sig_sig (hσσ : ∀ a : E, σ (σ a) = a) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by sorry
