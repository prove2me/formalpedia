-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_decomp
-- name    : PIW.AdelicOrbitU.decomp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:59.88081+00:00
-- url     : https://prove2.me/theorems/e6934ef1-bcad-5864-a243-42300dc7b334
-- title:
--   Adelic Orbit U: decomp
-- statement:
--   The Adelic Orbit U construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/StLamOf.lean#L140-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/StLamOf.lean#L140-L156

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
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
variable (R : Type) [CommRing R] [Algebra F R]

theorem PIW.AdelicOrbitU.decomp (θ : E) (hspan : ∀ e : E, ∃ p q : F, e = algebraMap F E p + algebraMap F E q * θ)
    (z : R ⊗[F] E) : ∃ a b : R, z = algebraMap R (R ⊗[F] E) a + algebraMap R (R ⊗[F] E) b * (1 ⊗ₜ θ) := by sorry
