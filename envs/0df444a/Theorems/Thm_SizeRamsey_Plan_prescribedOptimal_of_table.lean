-- Prove2me | Theorems.Thm_SizeRamsey_Plan_prescribedOptimal_of_table
-- name    : SizeRamsey.Plan.prescribedOptimal_of_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:21.467509+00:00
-- url     : https://prove2.me/theorems/0c76e18f-d445-414e-a680-d11b94b7f924
-- title:
--   Plan: prescribed Optimal of table
-- statement:
--   The Plan construction uses the prescribed Optimal of table property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L78-L86
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L78-L86

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.prescribedOptimal_of_table {V : Type*} [Fintype V] {G : SimpleGraph V} (k : ℕ)
    (P : V → Finset V)
    (hP : ∀ v, v ∈ P v ∧ (P v).card = k ∧ QTrans G (P v))
    (hlower : ∀ S : Finset V, S.card < k → ¬ c4Transversal G S) (v₀ : V) :
    tau4 G = k ∧ PrescribedOptimal G := by sorry
