-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CatCoh_Desc_Basis_eq_zero_of_local__b89555c1ea3b
-- name    : P2M_GlobalTheory_CatCoh_Desc_Basis_eq_zero_of_local__b89555c1ea3b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:14:53.709893+00:00
-- url     : https://prove2.me/theorems/9db5a95a-15d0-4dbb-b1a7-8b9bb4d9602d
-- title:
--   P2 M Global Theory Cat Coh Desc Basis eq zero of local  b89555c1ea3b: P2 M Global Theory Cat Coh Desc Basis eq zero of local  b89555c1ea3b
-- statement:
--   The P2 M Global Theory Cat Coh Desc Basis eq zero of local  b89555c1ea3b construction uses the P2 M Global Theory Cat Coh Desc Basis eq zero of local  b89555c1ea3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCocycleCoboundaryCommaLocalBasis.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCocycleCoboundaryCommaLocalBasis.lean#L35-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.Basis
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']

theorem P2M_GlobalTheory_CatCoh_Desc_Basis_eq_zero_of_local__b89555c1ea3b (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ t₃ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S))
    (h₃ : Nonempty (G.obj t₃ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → Nonempty (t₃ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by sorry

alias «GlobalTheory».«CatCoh».«Desc».«Basis».«eq_zero_of_local₃» := P2M_GlobalTheory_CatCoh_Desc_Basis_eq_zero_of_local__b89555c1ea3b
