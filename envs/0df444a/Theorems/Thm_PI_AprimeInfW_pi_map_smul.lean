-- Prove2me | Theorems.Thm_PI_AprimeInfW_pi_map_smul
-- name    : PI.AprimeInfW.pi_map_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:16:51.648208+00:00
-- url     : https://prove2.me/theorems/edbba7af-84d4-471e-9955-738144eb25ea
-- title:
--   Aprime Inf W: pi map smul
-- statement:
--   The Aprime Inf W construction uses the pi map smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PlaceAll.lean#L21-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PlaceAll.lean#L21-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PlaceAll
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
open MeasureTheory Matrix
open scoped ENNReal NNReal

theorem PI.AprimeInfW.pi_map_smul {V : Type} [Fintype V] {X Y : V → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, MeasurableSpace (Y v)] (μ : ∀ v, Measure (X v)) (ν : ∀ v, Measure (Y v)) [∀ v, SigmaFinite (ν v)]
    (f : ∀ v, X v → Y v) (hf : ∀ v, Measurable (f v)) (c : V → ℝ≥0)
    (hc : ∀ v, (μ v).map (f v) = c v • ν v) :
    (Measure.pi μ).map (fun x v => f v (x v)) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi ν := by sorry
