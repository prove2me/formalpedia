-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_coord_fwd
-- name    : ReciprocityTheory.AnForm.R.exists_coord_fwd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:10.275337+00:00
-- url     : https://prove2.me/theorems/c25533c1-4672-57f1-bb68-d7d563bbfb8d
-- title:
--   R: exists coord fwd
-- statement:
--   The R construction uses the exists coord fwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BijOnClosedPointsOfIsIso.lean#L95-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BijOnClosedPointsOfIsIso.lean#L95-L137

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BijOnClosedPointsOfIsIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W X : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.exists_coord_fwd (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (PW : AffPres sW) (V : X.Opens) {σ : Type} [Finite σ]
    (u : σ → Γ(X, V)) (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial (Fin PW.n) ℂ) (F : σ → MvPolynomial (Fin PW.n) ℂ),
        eval (PW.coord x hxW) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (PW.coord y hyW) q ≠ 0 ∧
          ∀ t, val sX (u t) (π.base y) hyV * eval (PW.coord y hyW) q =
            eval (PW.coord y hyW) (F t) := by sorry
