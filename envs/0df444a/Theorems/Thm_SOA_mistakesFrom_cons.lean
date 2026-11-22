-- Prove2me | Theorems.Thm_SOA_mistakesFrom_cons
-- name    : SOA_mistakesFrom_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:10.066037+00:00
-- url     : https://prove2.me/theorems/341ddb2b-cecf-4675-ae1c-a7a284a1c032
-- title:
--   SOA mistakes From cons: SOA mistakes From cons
-- statement:
--   SOA mistakesFrom cons: unfold one step using the interface.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L165-L169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L165-L169

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
set_option autoImplicit true
@[expose] public section
public section

theorem SOA_mistakesFrom_cons (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (c : X → Bool) (x : X) (xs : List X) :
    (SOA X C).mistakesFrom history c (x :: xs) =
      (if (SOA X C).predict history x ≠ c x then 1 else 0) +
        (SOA X C).mistakesFrom (history ++ [(x, c x)]) c xs := by sorry
