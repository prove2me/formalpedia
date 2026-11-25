-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_norm_Gs_add_sub_le_core
-- name    : ReciprocityTheory.Cheb.norm_Gs_add_sub_le_core
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:05.03162+00:00
-- url     : https://prove2.me/theorems/3f0d0c4d-8db8-5747-a7f1-5d4ea71cbc6e
-- title:
--   Cheb: norm Gs add sub le core
-- statement:
--   The Cheb construction uses the norm Gs add sub le core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L230-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L230-L289

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.norm_Gs_add_sub_le_core {l : ℕ} (χ : DirichletCharacter ℂ l) {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) 2)
    {A : ℝ} (hA : 0 ≤ A)
    (hAb : ∀ x y : mixedSpace E, ∑ i, |ucoord x i - ucoord y i| ≤ A * ‖logMap x - logMap y‖)
    {y k : mixedSpace E} {B a : ℝ} (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (ha2 : 2 ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) :
    ‖Gs χ s (y + k) - Gs χ s y‖ ≤
      (A * (4 * (2 * B / a)) + 2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a))) *
        ((a / 2) ^ Module.finrank ℚ E)⁻¹ := by sorry
