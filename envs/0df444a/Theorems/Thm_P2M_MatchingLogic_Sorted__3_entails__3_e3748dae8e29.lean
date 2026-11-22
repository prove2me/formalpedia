-- Prove2me | Theorems.Thm_P2M_MatchingLogic_Sorted__3_entails__3_e3748dae8e29
-- name    : P2M_MatchingLogic_Sorted__3_entails__3_e3748dae8e29
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:33.59477+00:00
-- url     : https://prove2.me/theorems/8954cd6c-c9a6-4ee2-a75e-054c71acbf79
-- title:
--   P2 M Matching Logic Sorted  3 entails  3 e3748dae8e29: P2 M Matching Logic Sorted  3 entails  3 e3748dae8e29
-- statement:
--   **Γ ⊨ φ.**
--
--   The paper: if `M_b` had distinct `r, s`, the valuation with `ρ(x) = r`,
--   `ρ(y) = s` gives `ρ(x ∧ y) = ∅`, and symbols propagate `∅`, so `ρ(f(x ∧ y)) = ∅`,
--   which is not `M_a` because carriers are nonempty. Hence `M_b` is a singleton,
--   every valuation sends `x` and `y` to the same element, and `ρ(g(x) ↔ g(y)) = M_c`
--   for every `ρ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L261-L346
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L261-L346

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type}

theorem P2M_MatchingLogic_Sorted__3_entails__3_e3748dae8e29 (x y : Var) (hxy : x ≠ y) :
    MGlobalCons (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y) := by sorry

alias «MatchingLogic».«Sorted».«Γ3_entails_φ3» := P2M_MatchingLogic_Sorted__3_entails__3_e3748dae8e29
