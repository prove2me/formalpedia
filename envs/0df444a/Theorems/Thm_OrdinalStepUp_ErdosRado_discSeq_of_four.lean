-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_discSeq_of_four
-- name    : OrdinalStepUp.ErdosRado.discSeq_of_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:30.355399+00:00
-- url     : https://prove2.me/theorems/cb4a65c2-122a-463c-8222-04e489c5b1cb
-- title:
--   Erdos Rado: disc Seq of four
-- statement:
--   The Erdos Rado construction uses the disc Seq of four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1076-L1085
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1076-L1085

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}

theorem OrdinalStepUp.ErdosRado.discSeq_of_four {u : FinChain (n + 4)}
    (h0 : u 0 = a) (h1 : u 1 = b) (h2 : u 2 = c) (h3 : u 3 = e) :
    discSeq u 0 = disc a b ∧ discSeq u 1 = disc b c ∧ discSeq u 2 = disc c e := by sorry
