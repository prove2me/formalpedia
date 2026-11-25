-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_quad_li
-- name    : PIW.AdelicOrbitU.quad_li
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:47:55.340523+00:00
-- url     : https://prove2.me/theorems/309db86c-8cc6-44a1-af8a-1da62ee89d16
-- title:
--   Adelic Orbit U: quad li
-- statement:
--   The Adelic Orbit U construction uses the quad li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L82-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/QuadFiniteDimensional.lean#L82-L98

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

theorem PIW.AdelicOrbitU.quad_li [CharZero F] {θ : E} (hθ0 : θ ≠ 0) (hσθ : σ θ = -θ) :
    LinearIndependent F ![(1 : E), θ] := by sorry
