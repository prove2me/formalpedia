-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_dzbEntry_symm
-- name    : ReciprocityTheory.AnForm.A.dzbEntry_symm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:21.950073+00:00
-- url     : https://prove2.me/theorems/4c645300-07d8-475e-8eac-775c7fbffe0b
-- title:
--   A: dzb Entry symm
-- statement:
--   The A construction uses the dzb Entry symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L60-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L60-L80

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.A.dzbEntry_symm {D : ℕ} (T : (Fin D → ℂ) →L[ℝ] BilinSp D)
    (hT : ∀ u x y, T u x y = T y x u) (k a b : Fin D) :
    (1 / 2 : ℂ) * hessEntry a b (T (Pi.single k 1)) +
        (Complex.I / 2) * hessEntry a b (T (Complex.I • Pi.single k 1)) =
      (1 / 2 : ℂ) * hessEntry a k (T (Pi.single b 1)) +
        (Complex.I / 2) * hessEntry a k (T (Complex.I • Pi.single b 1)) := by sorry
