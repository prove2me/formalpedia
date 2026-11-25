-- Prove2me | Theorems.Thm_PI_AprimeInfW_place_split
-- name    : PI.AprimeInfW.place_split
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:17:19.502515+00:00
-- url     : https://prove2.me/theorems/1978025f-62c4-5520-92c8-bc0382e526c6
-- title:
--   Aprime Inf W: place split
-- statement:
--   The Aprime Inf W construction uses the place split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PlaceAll.lean#L116-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PlaceAll.lean#L116-L216

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
set_option maxHeartbeats 800000

theorem PI.AprimeInfW.place_split {V : Type} [Fintype V] {a b : ℕ} {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin a) (Fin b) ℂ)) (Q : V → Matrix (Fin a) (Fin b) ℂ → Prop)
    (hQ : ∀ x v, Q v (L x v)) (hQ0 : ∀ v, Q v 0)
    (hn : ∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2)
    (hs : ∀ M : V → Matrix (Fin a) (Fin b) ℂ, (∀ v, Q v (M v)) → ∃ x, L x = M) :
    ∃ (κ : V → Type) (_ : ∀ v, Fintype (κ v)) (Lv : ∀ v, EuclideanSpace ℝ (κ v) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ)
      (T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (κ v)),
      (∀ v y, Q v (Lv v y)) ∧ (∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2) ∧
      (∀ v M, Q v M → ∃ y, Lv v y = M) ∧ (∀ x v, Lv v (T x v) = L x v) ∧ Function.Bijective T ∧
      (∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) := by sorry
