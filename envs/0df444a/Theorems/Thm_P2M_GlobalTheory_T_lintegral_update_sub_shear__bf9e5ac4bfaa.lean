-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_lintegral_update_sub_shear__bf9e5ac4bfaa
-- name    : P2M_GlobalTheory_T_lintegral_update_sub_shear__bf9e5ac4bfaa
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:37:46.546034+00:00
-- url     : https://prove2.me/theorems/807d5465-e868-4a1b-96a3-c424ca6e754f
-- title:
--   P2 M Global Theory T lintegral update sub shear  bf9e5ac4bfaa: P2 M Global Theory T lintegral update sub shear  bf9e5ac4bfaa
-- statement:
--   The P2 M Global Theory T lintegral update sub shear  bf9e5ac4bfaa construction uses the P2 M Global Theory T lintegral update sub shear  bf9e5ac4bfaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralUpdateSubShearStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralUpdateSubShearStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUpdateSubShear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUpdateSubShearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_lintegral_update_sub_shear__bf9e5ac4bfaa : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (g : (ι → ℂ) → ℂ), Measurable g → (∀ w v : ι → ℂ, (∀ j, j ≠ i → w j = v j) → g w = g v) → ∀ F : (ι → ℂ) → ℝ≥0∞, Measurable F → ∫⁻ w, F (Function.update w i (w i - g w)) = ∫⁻ w, F w := by sorry

alias «GlobalTheory».«T».«lintegral_update_sub_shear'» := P2M_GlobalTheory_T_lintegral_update_sub_shear__bf9e5ac4bfaa
