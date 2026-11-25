-- Prove2me | Theorems.Thm_SNumbers_signedSum_insert_of_notMem
-- name    : SNumbers.signedSum_insert_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:24:59.160708+00:00
-- url     : https://prove2.me/theorems/d87cbe73-088c-56fb-bf93-1b87855132a8
-- title:
--   SNumbers: signed Sum insert of not Mem
-- statement:
--   Adding a new index `a ∉ J` outside the sign pattern subtracts `w a`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L76-L80
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L76-L80

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

theorem SNumbers.signedSum_insert_of_notMem {w : ι → G} {a : ι} {S J : Finset ι}
    (ha : a ∉ J) (haS : a ∉ S) :
    signedSum w S (insert a J) = signedSum w S J - w a := by sorry
