-- Prove2me | Theorems.Thm_ProbabilityTheory_exists_randomized_inverse
-- name    : ProbabilityTheory.exists_randomized_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:59.78319+00:00
-- url     : https://prove2.me/theorems/3452cd11-7b8d-4974-a4e3-df60ab74e7ef
-- title:
--   Probability Theory: exists randomized inverse
-- statement:
--   A measurable map of a uniform variable has a randomized inverse that recovers
--   the uniform law and inverts the map almost everywhere.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/RandomizedInverse.lean#L27-L57
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/RandomizedInverse.lean#L27-L57

module
public import Mathlib.Probability.Kernel.Representation
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Definitions.Def_LeanPool_Copula_Distribution_RandomizedInverse
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter Function
open scoped unitInterval
open ProbabilityTheory

theorem ProbabilityTheory.exists_randomized_inverse {B : Type*} [MeasurableSpace B] [StandardBorelSpace B]
    (q : I → B) (hq : Measurable q) :
    ∃ g : B → I → I, Measurable (uncurry g) ∧
      ((volume.map q).prod volume).map (uncurry g) = volume ∧
      ∀ᵐ p ∂((volume.map q).prod volume), q (g p.1 p.2) = p.1 := by sorry
