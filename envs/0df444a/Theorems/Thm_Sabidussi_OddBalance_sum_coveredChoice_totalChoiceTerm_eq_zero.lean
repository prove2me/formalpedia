-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_sum_coveredChoice_totalChoiceTerm_eq_zero
-- name    : Sabidussi.OddBalance.sum_coveredChoice_totalChoiceTerm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:57.055568+00:00
-- url     : https://prove2.me/theorems/ddafcaee-89e6-5b93-8541-d71f24f5bbbd
-- title:
--   Odd Balance: sum covered Choice total Choice Term eq zero
-- statement:
--   The Odd Balance construction uses the sum covered Choice total Choice Term eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L429-L444
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L429-L444

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

theorem Sabidussi.OddBalance.sum_coveredChoice_totalChoiceTerm_eq_zero
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) :
    (∑ c : CoveredChoice S, totalChoiceTerm b S c.1) = 0 := by sorry
