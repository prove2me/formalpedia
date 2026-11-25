-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_ratio_core
-- name    : ReciprocityTheory.AnForm.R.exists_ratio_core
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:39:32.44931+00:00
-- url     : https://prove2.me/theorems/4df601d0-51b1-4dee-a024-f9c8966684ce
-- title:
--   R: exists ratio core
-- statement:
--   The R construction uses the exists ratio core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SecHomSurjective.lean#L94-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SecHomSurjective.lean#L94-L192

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective
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
variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.exists_ratio_core {S T : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (t : T ⟶ Spec (.of ℂ))
    (g : S ⟶ T) (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t]
    (V : T.Opens) (hV : IsAffineOpen V) {σ : Type} (u : σ → Γ(T, V))
    (hu : ∀ a : Γ(T, V), ∃ F : MvPolynomial σ ℂ, a = eval₂ (constSec t V) u F)
    {ι : Type} [Finite ι] (Ω : S.Opens) (e : ι → Γ(S, Ω)) (x : S) (hxΩ : x ∈ Ω)
    (hxV : g.base x ∈ V) (hc : IsClosed ({x} : Set S))
    (hsurj : Function.Surjective (g.stalkMap x)) :
    ∃ O : S.Opens, x ∈ O ∧ O ≤ Ω ⊓ g ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial σ ℂ) (F : ι → MvPolynomial σ ℂ),
        eval (fun a => val t (u a) (g.base x) hxV) q ≠ 0 ∧
        ∀ (y : S) (hyΩ : y ∈ Ω) (hyV : g.base y ∈ V), y ∈ O → IsClosed ({y} : Set S) →
          eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 ∧
          ∀ i, val s (e i) y hyΩ * eval (fun a => val t (u a) (g.base y) hyV) q =
            eval (fun a => val t (u a) (g.base y) hyV) (F i) := by sorry
