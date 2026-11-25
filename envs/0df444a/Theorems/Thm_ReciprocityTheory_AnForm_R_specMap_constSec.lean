-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_specMap_constSec
-- name    : ReciprocityTheory.AnForm.R.specMap_constSec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:10:05.646845+00:00
-- url     : https://prove2.me/theorems/dc64c146-873d-4bca-bbc9-a7f78309182d
-- title:
--   R: spec Map const Sec
-- statement:
--   The R construction uses the spec Map const Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L33-L38

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section

theorem ReciprocityTheory.AnForm.R.specMap_constSec {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (U : S.affineOpens) :
    Spec.map (CommRingCat.ofHom (constSec s U.1)) = U.2.fromSpec ≫ s := by sorry
