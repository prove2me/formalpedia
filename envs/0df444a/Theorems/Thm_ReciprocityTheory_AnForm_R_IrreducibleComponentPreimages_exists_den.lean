-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_den
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_den
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:40:45.095021+00:00
-- url     : https://prove2.me/theorems/8a3d1f5c-d965-46d5-81d6-2013e57f7dbf
-- title:
--   Irreducible Component Preimages: exists den
-- statement:
--   The Irreducible Component Preimages construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L245-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L245-L327

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {W : Scheme.{0}}
variable {s : W ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_den (P : AffPres s) (x : W) (hx : x ∈ P.V) (hcl : IsClosed ({x} : Set W))
    (hV : IsAffineOpen P.V) (I : Ideal Γ(W, P.V)) {ι : Type*} (J : Finset ι)
    (a b : ι → MvPolynomial (Fin P.n) ℂ) (hb : ∀ l, eval (P.coord x hx) (b l) ≠ 0)
    (t : W.presheaf.stalk x) (hst : I.map (W.presheaf.germ P.V x hx).hom = Ideal.span {t})
    (ht : W.presheaf.germ P.V x hx (P.secHom (∏ l ∈ J, a l)) =
      t * ∏ l ∈ J, W.presheaf.germ P.V x hx (P.secHom (b l)))
    (hprod : P.stalkEquiv x hx hcl t * algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, b l) =
      algebraMap _ (locRing P.K (P.coord x hx)) (∏ l ∈ J, a l)) :
    ∃ h, eval (P.coord x hx) h ≠ 0 ∧ h * ∏ l ∈ J, a l ∈ I.comap P.secHom ∧
      ∀ g ∈ I.comap P.secHom, h * g ∈ Ideal.span {∏ l ∈ J, a l} ⊔ P.K := by sorry
