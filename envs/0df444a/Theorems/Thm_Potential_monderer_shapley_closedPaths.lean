-- Prove2me | Theorems.Thm_Potential_monderer_shapley_closedPaths
-- name    : Potential.monderer_shapley_closedPaths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:58:53.826663+00:00
-- url     : https://prove2.me/theorems/c32222eb-f25a-4255-b38b-25be0e13180d
-- title:
--   Potential: monderer shapley closed Paths
-- statement:
--   Monderer–Shapley (1996), Theorem 2.8, closed-path formulation. All finite
--   paths are quantified; action spaces need not be finite.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L441-L447
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L441-L447

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

theorem Potential.monderer_shapley_closedPaths (u : Payoff A) :
    (∃ P : Profile A → ℝ, ExactPotential u P) ↔ ClosedPathProperty u := by sorry
