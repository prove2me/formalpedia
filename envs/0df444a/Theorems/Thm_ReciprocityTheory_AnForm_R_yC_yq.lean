-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_yC_yq
-- name    : ReciprocityTheory.AnForm.R.yC_yq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:40.07349+00:00
-- url     : https://prove2.me/theorems/ed81ba07-b518-510c-8474-a6170cdc2b0f
-- title:
--   R: y C yq
-- statement:
--   The R construction uses the y C yq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L89-L93

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
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.yC_yq {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) (q : Σ k, ι k) :
    yC hP p g i (finSumFinEquiv (Sum.inl (Fintype.equivFin _ q))) =
      algebraMap _ (FinalTheorems.reesChart g i) (chartCoord hP p q) := by sorry
