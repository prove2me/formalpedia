-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zsmul__b8e6a11e43d5
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zsmul__b8e6a11e43d5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:17:24.135929+00:00
-- url     : https://prove2.me/theorems/1f3e3cbf-dc43-444c-85c7-28622c3d9bcc
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 Is U zsmul  b8e6a11e43d5: P2 M Reciprocity Theory Chart Restriction G I2 Is U zsmul  b8e6a11e43d5
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 Is U zsmul  b8e6a11e43d5 construction uses the P2 M Reciprocity Theory Chart Restriction G I2 Is U zsmul  b8e6a11e43d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitU.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitU.lean#L27-L36

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zsmul__b8e6a11e43d5 {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (k : ℤ) (hu : IsU I x u) :
    IsU I (k • x) (k • u) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«IsU».«zsmul'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zsmul__b8e6a11e43d5
