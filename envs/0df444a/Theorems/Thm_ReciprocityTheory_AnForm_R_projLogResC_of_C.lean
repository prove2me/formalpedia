-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_projLogResC_of_C
-- name    : ReciprocityTheory.AnForm.R.projLogResC_of_C
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:55:22.770835+00:00
-- url     : https://prove2.me/theorems/f440cc2d-79a7-5255-b7c8-1fd9fe775120
-- title:
--   R: proj Log Res C of C
-- statement:
--   The R construction uses the proj Log Res C of C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjLogResCOfCR.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjLogResCOfCR.lean#L25-L28

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjLogResCOfCR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R

theorem ReciprocityTheory.AnForm.R.projLogResC_of_C (hC : FinalTheorems.GFLogStC) (hQ : FinalTheorems.FinTypeQE) : ProjLogResC := by sorry
