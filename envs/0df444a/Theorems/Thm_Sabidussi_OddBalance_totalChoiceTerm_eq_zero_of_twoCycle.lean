-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_totalChoiceTerm_eq_zero_of_twoCycle
-- name    : Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_twoCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:43.494181+00:00
-- url     : https://prove2.me/theorems/a1f6804a-baeb-4895-a029-0b7c825451cf
-- title:
--   Odd Balance: total Choice Term eq zero of two Cycle
-- statement:
--   The Odd Balance construction uses the total Choice Term eq zero of two Cycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L205-L258
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L205-L258

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Sabidussi.OddBalance.totalChoiceTerm_eq_zero_of_twoCycle
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (f : Choice S) (v₀ v₁ : {v // v ∈ S})
    (hne : v₀ ≠ v₁)
    (hf₀ : (f v₀ : V) = v₁) (hf₁ : (f v₁ : V) = v₀)
    (hu₀ : ∀ v, (f v : V) = v₀ → v = v₁)
    (hu₁ : ∀ v, (f v : V) = v₁ → v = v₀) :
    totalChoiceTerm b S f = 0 := by sorry
