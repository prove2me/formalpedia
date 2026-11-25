-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_filt_ball
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.filt_ball
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:17.422549+00:00
-- url     : https://prove2.me/theorems/36105de3-0fbb-43c5-9c11-1fa9b3da3956
-- title:
--   Units Filt: filt ball
-- statement:
--   The Units Filt construction uses the filt ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandD.lean#L13-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandD.lean#L13-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
open Finset
variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.filt_ball {A C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hA1 : ∀ x : L, ‖x‖ ≤ A * ‖Phi K L x‖) (hA : 0 ≤ A)
    (hC1 : ∀ x y : L, ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖)
    (hAρ : A * ρ < 1) (hCρ : C * ρ ≤ 1 / 2) :
    Filt (L ≃ₐ[K] L) (fun n => ball K L (ρ * (1 / 2 : ℝ) ^ n) (rad_nonneg hρ n)) (proj1 K L) := by sorry
