-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_inter_reesCharts__6b26385361aa
-- name    : P2M_ReciprocityTheory_AnForm_R_inter_reesCharts__6b26385361aa
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:31:27.481948+00:00
-- url     : https://prove2.me/theorems/1dfab093-691d-5f56-8203-eefd906f171b
-- title:
--   P2 M Reciprocity Theory An Form R inter rees Charts  6b26385361aa: P2 M Reciprocity Theory An Form R inter rees Charts  6b26385361aa
-- statement:
--   The P2 M Reciprocity Theory An Form R inter rees Charts  6b26385361aa construction uses the P2 M Reciprocity Theory An Form R inter rees Charts  6b26385361aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsB.lean#L91-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsB.lean#L91-L187

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section

theorem P2M_ReciprocityTheory_AnForm_R_inter_reesCharts__6b26385361aa {X W : Scheme.{0}} (π : W ⟶ X) (J : X.IdealSheafData) (hB : FinalTheorems.Blowup π J)
    (U : X.affineOpens) {m : ℕ} (g : Fin m → Γ(X, U.1)) (hg : Ideal.span (Set.range g) = J.ideal U)
    (V : Fin m → W.Opens) (hV : ∀ i, V i ≤ π ⁻¹ᵁ U.1)
    (e : ∀ i, (V i).toScheme ≅ Spec (CommRingCat.of (FinalTheorems.reesChart g i)))
    (he : ∀ i, (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (FinalTheorems.reesChart g i))) ≫
      U.2.fromSpec = (V i).ι ≫ π)
    (i j : Fin m) (t : Γ(W, V i))
    (ht : t = (V i).topIso.hom ((e i).hom.appTop ((Scheme.ΓSpecIso _).inv
      ⟨IsLocalization.mk' (Localization.Away (g i)) (g j) (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)),
        Algebra.subset_adjoin ⟨j, rfl⟩⟩))) :
    V i ⊓ V j = W.basicOpen t := by sorry

alias «ReciprocityTheory».«AnForm».«R».«inter_reesCharts'» := P2M_ReciprocityTheory_AnForm_R_inter_reesCharts__6b26385361aa
