-- Prove2me | Theorems.Thm_Potential_exactPotential_maximizer_pureNash
-- name    : Potential.exactPotential_maximizer_pureNash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:00:34.712629+00:00
-- url     : https://prove2.me/theorems/19ddc919-7f85-5ea3-8908-5e09f1a1913f
-- title:
--   Potential: exact Potential maximizer pure Nash
-- statement:
--   An exact potential's global maximizer is a pure Nash equilibrium.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L451-L456
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L451-L456

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Definitions.Def_MondererShapley_Solution
set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Nonempty (A i)]
omit [Fintype I] [∀ i, Nonempty (A i)]

theorem Potential.exactPotential_maximizer_pureNash (u : Payoff A) (P : Profile A → ℝ)
    (hp : ExactPotential u P) (s : Profile A) (hs : ∀ t, P t ≤ P s) : PureNash u s := by sorry
