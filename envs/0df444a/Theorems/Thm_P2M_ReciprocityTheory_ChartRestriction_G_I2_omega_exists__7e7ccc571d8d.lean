-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_omega_exists__7e7ccc571d8d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_omega_exists__7e7ccc571d8d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:59.796369+00:00
-- url     : https://prove2.me/theorems/3c580794-0bbf-4f2c-8c62-7ddc18d9e99b
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 omega exists  7e7ccc571d8d: P2 M Reciprocity Theory Chart Restriction G I2 omega exists  7e7ccc571d8d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 omega exists  7e7ccc571d8d construction uses the P2 M Reciprocity Theory Chart Restriction G I2 omega exists  7e7ccc571d8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitO.lean#L62-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitO.lean#L62-L337

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitOA
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_omega_exists__7e7ccc571d8d [IsCMField E] : ∃ (n : ℕ) (ω : Fin n → 𝓞 E),
    (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ omStar (E := E)) ∧
      ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«omega_exists'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_omega_exists__7e7ccc571d8d
