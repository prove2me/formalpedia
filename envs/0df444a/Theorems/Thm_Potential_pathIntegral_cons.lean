-- Prove2me | Theorems.Thm_Potential_pathIntegral_cons
-- name    : Potential.pathIntegral_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:51:58.440457+00:00
-- url     : https://prove2.me/theorems/a0fe1c76-4f08-424c-b304-6d56cc936775
-- title:
--   Potential: path Integral cons
-- statement:
--   The Potential construction uses the path Integral cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L85-L91
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L85-L91

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

theorem Potential.pathIntegral_cons {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (s : Profile A) (m : Move A) (ms : List (Move A)) :
    pathIntegral u s (m :: ms) = u m.1 (Function.update s m.1 m.2) - u m.1 s +
      pathIntegral u (Function.update s m.1 m.2) ms := by sorry
