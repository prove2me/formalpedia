-- Prove2me | Theorems.Thm_PI_AprimeInfW_mp_of_isom
-- name    : PI.AprimeInfW.mp_of_isom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:24.661796+00:00
-- url     : https://prove2.me/theorems/9ea126a4-91bd-4213-9972-52180df2b5f2
-- title:
--   Aprime Inf W: mp of isom
-- statement:
--   The Aprime Inf W construction uses the mp of isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/MpOfIsomProd.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/MpOfIsomProd.lean#L17-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MpOfIsomProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix ComplexConjugate
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem PI.AprimeInfW.mp_of_isom (f : E →ₗ[ℝ] F) (hn : ∀ x, ‖f x‖ = ‖x‖) (hs : Function.Surjective f) :
    MeasurePreserving f volume volume := by sorry
