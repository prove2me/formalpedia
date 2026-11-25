-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_chart_aff
-- name    : ReciprocityTheory.AnForm.R.chart_aff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:43:19.957083+00:00
-- url     : https://prove2.me/theorems/01c0acf6-7499-414a-9064-1deea41c72a3
-- title:
--   R: chart aff
-- statement:
--   The R construction uses the chart aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WCharts.lean#L59-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WCharts.lean#L59-L84

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WCharts
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

theorem ReciprocityTheory.AnForm.R.chart_aff {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {W : Scheme.{0}} (π : W ⟶ projX P hP) {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1))
    (i : Fin m) (V : W.Opens) (e : V.toScheme ≅ Spec (.of (FinalTheorems.reesChart g i)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(projX P hP, (chartOpen hP p).1)
      (FinalTheorems.reesChart g i))) ≫ (chartOpen hP p).2.fromSpec = V.ι ≫ π) :
    ∃ (I : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ))
      (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ ⧸ I)))
      (hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ ⧸ I))) = V.ι ≫ (π ≫ toSpecC hP)),
      ∀ l, (AffPres.mk V _ I iso hiso : AffPres (π ≫ toSpecC hP)).secHom (X l) =
        V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso _).inv (yC hP p g i l))) := by sorry
