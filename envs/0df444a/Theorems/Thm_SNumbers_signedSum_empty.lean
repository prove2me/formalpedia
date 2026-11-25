-- Prove2me | Theorems.Thm_SNumbers_signedSum_empty
-- name    : SNumbers.signedSum_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:42:34.842956+00:00
-- url     : https://prove2.me/theorems/860c285b-88a6-4ab1-840b-50a5b10c87d4
-- title:
--   SNumbers: signed Sum empty
-- statement:
--   The signed sum over the empty index set is `0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L72-L73
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L72-L73

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers
variable {G : Type*} [AddCommGroup G] {ι : Type*} [DecidableEq ι]

theorem SNumbers.signedSum_empty (w : ι → G) (S : Finset ι) : signedSum w S ∅ = 0 := by sorry
