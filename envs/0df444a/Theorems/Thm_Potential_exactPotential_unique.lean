-- Prove2me | Theorems.Thm_Potential_exactPotential_unique
-- name    : Potential.exactPotential_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:03:29.722978+00:00
-- url     : https://prove2.me/theorems/1bdd33d2-20db-5c07-8f29-46c1544c1614
-- title:
--   Potential: exact Potential unique
-- statement:
--   All exact potentials differ by a constant, even with infinite action sets.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L306-L319
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L306-L319

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
variable {I : Type*} {A : I → Type*} [DecidableEq I]

theorem Potential.exactPotential_unique [Fintype I] [∀ i, Nonempty (A i)]
    (u : Payoff A) (P Q : Profile A → ℝ)
    (hp : ExactPotential u P) (hq : ExactPotential u Q) :
    ∃ c : ℝ, ∀ s, P s = Q s + c := by sorry
