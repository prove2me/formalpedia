-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hessEntry_apply
-- name    : ReciprocityTheory.AnForm.A.hessEntry_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:32.11027+00:00
-- url     : https://prove2.me/theorems/00d115b9-5c92-4300-bcf8-0c4fcabf7683
-- title:
--   A: hess Entry apply
-- statement:
--   The A construction uses the hess Entry apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L107-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L107-L117

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.A.hessEntry_apply {D : ℕ} (a b : Fin D) (H : BilinSp D) :
    hessEntry a b H =
      ((H (Pi.single a 1) (Pi.single b 1) +
          H (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1) : ℝ) +
        Complex.I * ((H (Pi.single a 1) (Complex.I • Pi.single b 1) -
          H (Complex.I • Pi.single a 1) (Pi.single b 1) : ℝ))) / 4 := by sorry
