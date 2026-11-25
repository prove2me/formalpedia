-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_algebraMap_reesChart_eq
-- name    : ReciprocityTheory.AnForm.R.algebraMap_reesChart_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:06:49.959596+00:00
-- url     : https://prove2.me/theorems/afd0f100-2b6b-597c-87f7-22136c801aac
-- title:
--   R: algebra Map rees Chart eq
-- statement:
--   The R construction uses the algebra Map rees Chart eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L17-L21

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

theorem ReciprocityTheory.AnForm.R.algebraMap_reesChart_eq {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i k : Fin m) :
    algebraMap R (FinalTheorems.reesChart g i) (g k) = fracR g i k * algebraMap R (FinalTheorems.reesChart g i) (g i) := by sorry
