-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_equiv_8b881e320897
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_equiv_8b881e320897
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:37:06.369503+00:00
-- url     : https://prove2.me/theorems/d041dc77-d1a9-5458-b04f-55d968d218c3
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow equiv 8b881e320897: P2 M Ground Theory Heights  Heights Objects Chow equiv 8b881e320897
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow equiv 8b881e320897 construction uses the P2 M Ground Theory Heights  Heights Objects Chow equiv 8b881e320897 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L105-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L105-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_equiv_8b881e320897 :
    (∀ (n : ℕ) (u : Fin n → ℤ), rename (blk n) (linForm u) = IndefiniteRowSideFullHecke.ArithBezout.linForm u) ∧
    (∀ (n : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
      linForm u ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P ↔ IndefiniteRowSideFullHecke.ArithBezout.linForm u ∈ P) ∧
    (∀ (R : Type) [CommRing R] (n e : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) R)
      (u : Fin n → R), specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) ∧
    (∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (n e : ℕ)
      (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R),
      map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f)) ∧
    (∀ (R : Type) [CommSemiring R] (n e δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) R),
      IsMultiHomog δ f ↔ IsMultihomog f δ) ∧
    (∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
        (map (Rat.castHom ℂ) f) → IsMultiHomog δ f) ∧
    (∀ (n : ℕ) (W : Ideal (MRing (PBlk n))),
      IsRelevant (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W) ∧
    (∀ (F : Type) [Field F] (n k : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
      IsChowFormCycle Z k f ↔ ∃ c : F, c ≠ 0 ∧
        ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
          (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z g) ∧
    (∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
      (f : MvPolynomial (Fin k × Fin n) F) (c : F),
      IsChowForm I k f → c ≠ 0 → IsChowForm I k (C c * f)) ∧
    (∀ (F : Type) [Field F] (n k δ : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
      (f : MvPolynomial (Fin k × Fin n) F),
      0 < k → IsChowForm I k f → IsMultiHomog δ f → chowDegree I k = δ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«equiv» := P2M_GroundTheory_Heights__Heights_ObjectsChow_equiv_8b881e320897
