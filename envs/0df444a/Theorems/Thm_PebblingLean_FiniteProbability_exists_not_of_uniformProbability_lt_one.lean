-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_exists_not_of_uniformProbability_lt_one
-- name    : PebblingLean.FiniteProbability.exists_not_of_uniformProbability_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:09.646613+00:00
-- url     : https://prove2.me/theorems/0ed18ad3-42bf-4f14-8c43-d0c2d192139f
-- title:
--   Finite Probability: exists not of uniform Probability lt one
-- statement:
--   The Finite Probability construction uses the exists not of uniform Probability lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/FiniteProbability.lean#L46-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/FiniteProbability.lean#L46-L62

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω ι : Type*}

theorem PebblingLean.FiniteProbability.exists_not_of_uniformProbability_lt_one [Fintype Ω] [Nonempty Ω]
    {P : Ω → Prop} [DecidablePred P]
    (hprob : uniformProbability P < 1) :
    ∃ ω : Ω, ¬ P ω := by sorry
