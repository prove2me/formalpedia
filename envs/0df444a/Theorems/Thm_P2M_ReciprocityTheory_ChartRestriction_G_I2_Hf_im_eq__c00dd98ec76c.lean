-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_eq__c00dd98ec76c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_eq__c00dd98ec76c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:15:49.770135+00:00
-- url     : https://prove2.me/theorems/bab1e990-7964-572a-98f2-20dbaabec490
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 Hf im eq  c00dd98ec76c: P2 M Reciprocity Theory Chart Restriction G I2 Hf im eq  c00dd98ec76c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 Hf im eq  c00dd98ec76c construction uses the P2 M Reciprocity Theory Chart Restriction G I2 Hf im eq  c00dd98ec76c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L37-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
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
variable {ι : Type} [Fintype ι]

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_eq__c00dd98ec76c (v w : EuclideanSpace ℂ ι) : (Hf v w).im = ⟪-(Complex.I • v), w⟫_ℝ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«Hf_im_eq'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_eq__c00dd98ec76c
