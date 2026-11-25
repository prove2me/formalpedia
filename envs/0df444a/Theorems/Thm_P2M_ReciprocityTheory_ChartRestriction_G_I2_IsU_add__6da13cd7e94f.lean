-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_add__6da13cd7e94f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_add__6da13cd7e94f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:56.858802+00:00
-- url     : https://prove2.me/theorems/385c7203-224a-51ec-8b25-695313dd12a9
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 Is U add  6da13cd7e94f: P2 M Reciprocity Theory Chart Restriction G I2 Is U add  6da13cd7e94f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 Is U add  6da13cd7e94f construction uses the P2 M Reciprocity Theory Chart Restriction G I2 Is U add  6da13cd7e94f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitU.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitU.lean#L17-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
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
variable {dim : (E →+* ℂ) → ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_add__6da13cd7e94f {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim} (hu : IsU I x u)
    (hv : IsU I y v) : IsU I (x + y) (u + v) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«IsU».«add'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_add__6da13cd7e94f
