-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_coord_inv
-- name    : ReciprocityTheory.AnForm.R.exists_coord_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:17.2118+00:00
-- url     : https://prove2.me/theorems/73023f6a-bd70-5b99-a347-81e8492ddeaf
-- title:
--   R: exists coord inv
-- statement:
--   The R construction uses the exists coord inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BijOnClosedPointsOfIsIso.lean#L63-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BijOnClosedPointsOfIsIso.lean#L63-L93

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

theorem ReciprocityTheory.AnForm.R.exists_coord_inv (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] (PW : AffPres sW) (V : X.Opens)
    (hV : IsAffineOpen V) {σ : Type} [Finite σ] (u : σ → Γ(X, V))
    (hu : ∀ t : Γ(X, V), ∃ F : MvPolynomial σ ℂ, t = eval₂ (constSec sX V) u F)
    (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V) (hxU : π.base x ∈ U)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ (U ⊓ V) ∧
      ∃ (q : MvPolynomial σ ℂ) (F : Fin PW.n → MvPolynomial σ ℂ),
        eval (fun t => val sX (u t) (π.base x) hxV) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (fun t => val sX (u t) (π.base y) hyV) q ≠ 0 ∧
          ∀ l, PW.coord y hyW l * eval (fun t => val sX (u t) (π.base y) hyV) q =
            eval (fun t => val sX (u t) (π.base y) hyV) (F l) := by sorry
