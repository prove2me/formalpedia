-- Prove2me | Theorems.Thm_UlmsTheorem_iso_of_ulmInvariant_eq_of_backAndForth
-- name    : UlmsTheorem.iso_of_ulmInvariant_eq_of_backAndForth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:54.912503+00:00
-- url     : https://prove2.me/theorems/8d3b4ae2-de41-4bff-acbf-83ff1b75167a
-- title:
--   Ulms Theorem: iso of ulm Invariant eq of back And Forth
-- statement:
--   Back-and-forth assembly: abstract `hforth`/`hback` hypotheses for `BFIsoStep`
--   imply the two groups are isomorphic.  Proved in full; no open obligation within.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Classification.lean#L272-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Classification.lean#L272-L284

module
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Classification
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
omit hp

theorem UlmsTheorem.iso_of_ulmInvariant_eq_of_backAndForth
    [Countable G] [Countable H]
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H)) :
    Nonempty (G ≃+ H) := by sorry
