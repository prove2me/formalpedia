-- Prove2me | Theorems.Thm_PI_LPI_prV_sum_tmul
-- name    : PI.LPI.prV_sum_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:11.615803+00:00
-- url     : https://prove2.me/theorems/c0f0780c-d31e-4ac2-be39-3a3f2c0b3215
-- title:
--   LPI: pr V sum tmul
-- statement:
--   The LPI construction uses the pr V sum tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/PrVSumTmul.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/PrVSumTmul.lean#L33-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.LPI
open Formalism.UG

theorem PI.LPI.prV_sum_tmul {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (e : Fin k → E) (a : Fin k → FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (∑ i, e i ⊗ₜ[F] a i) = ∑ i, e i ⊗ₜ[F] a i v := by sorry
