-- Prove2me | Theorems.Thm_Potential_exactPotential_pathIntegral
-- name    : Potential.exactPotential_pathIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:52:04.555408+00:00
-- url     : https://prove2.me/theorems/2c0627d0-f68b-50af-aca1-06f7e82f45a6
-- title:
--   Potential: exact Potential path Integral
-- statement:
--   An exact potential makes every path integral telescope.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L210-L218
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L210-L218

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

theorem Potential.exactPotential_pathIntegral (u : Payoff A) (P : Profile A → ℝ)
    (hp : ExactPotential u P) (s : Profile A) (ms : List (Move A)) :
    pathIntegral u s ms = P (endpoint s ms) - P s := by sorry
