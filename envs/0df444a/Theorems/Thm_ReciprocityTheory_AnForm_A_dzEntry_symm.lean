-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_dzEntry_symm
-- name    : ReciprocityTheory.AnForm.A.dzEntry_symm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:17.026194+00:00
-- url     : https://prove2.me/theorems/cfdf7348-f29c-40e5-9c73-c7d605522112
-- title:
--   A: dz Entry symm
-- statement:
--   The A construction uses the dz Entry symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L43-L58

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

theorem ReciprocityTheory.AnForm.A.dzEntry_symm {D : ℕ} (T : (Fin D → ℂ) →L[ℝ] BilinSp D) (hT : ∀ u x, T u x = T x u)
    (j a b : Fin D) :
    (1 / 2 : ℂ) * hessEntry a b (T (Pi.single j 1)) +
        (-(Complex.I / 2)) * hessEntry a b (T (Complex.I • Pi.single j 1)) =
      (1 / 2 : ℂ) * hessEntry j b (T (Pi.single a 1)) +
        (-(Complex.I / 2)) * hessEntry j b (T (Complex.I • Pi.single a 1)) := by sorry
