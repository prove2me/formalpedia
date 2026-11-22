-- Prove2me | Theorems.Thm_Parikh_isRegular_of_finite_language_cover
-- name    : Parikh.isRegular_of_finite_language_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:44.829006+00:00
-- url     : https://prove2.me/theorems/8b6acd05-28ae-4690-bb70-cc8a3579458f
-- title:
--   Parikh: is Regular of finite language cover
-- statement:
--   A finite family of languages covering every one-letter continuation gives
--   a finite NFA. Transitions are sound language inclusions, and the cover hypothesis
--   ensures completeness; determinization is Mathlib's existing construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L44-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L44-L90

module
public import Mathlib.Computability.DFA
public import Mathlib.Computability.NFA
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
set_option autoImplicit true
@[expose] public section
public section
open scoped Computability
open Parikh
variable {T : Type*}

theorem Parikh.isRegular_of_finite_language_cover (L : Language T)
    (F : Set (Language T)) (hF : F.Finite) (hL : L ∈ F)
    (hcover : ∀ K ∈ F, ∀ a w, a :: w ∈ K →
      ∃ J ∈ F, w ∈ J ∧ ∀ v ∈ J, a :: v ∈ K) : L.IsRegular := by sorry
