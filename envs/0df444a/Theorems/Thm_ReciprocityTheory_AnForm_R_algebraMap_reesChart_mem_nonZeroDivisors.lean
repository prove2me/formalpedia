-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_algebraMap_reesChart_mem_nonZeroDivisors
-- name    : ReciprocityTheory.AnForm.R.algebraMap_reesChart_mem_nonZeroDivisors
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:37.849903+00:00
-- url     : https://prove2.me/theorems/7773822c-b848-4ae5-917b-be23bd5ae4d6
-- title:
--   R: algebra Map rees Chart mem non Zero Divisors
-- statement:
--   The R construction uses the algebra Map rees Chart mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L23-L31

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

theorem ReciprocityTheory.AnForm.R.algebraMap_reesChart_mem_nonZeroDivisors {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R)
    (i : Fin m) : algebraMap R (FinalTheorems.reesChart g i) (g i) ∈ nonZeroDivisors (FinalTheorems.reesChart g i) := by sorry
