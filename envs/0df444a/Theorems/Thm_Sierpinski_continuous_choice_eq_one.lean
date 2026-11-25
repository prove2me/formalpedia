-- Prove2me | Theorems.Thm_Sierpinski_continuous_choice_eq_one
-- name    : Sierpinski.continuous_choice_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:53:56.530751+00:00
-- url     : https://prove2.me/theorems/cae43531-114f-574c-bc44-1a0876e53e08
-- title:
--   Sierpinski: continuous choice eq one
-- statement:
--   A continuous choice among a countable family of continuous functions that
--   are everywhere pairwise distinct uses one fixed function on a continuum.
--
--   Source: https://github.com/Arthur742Ramos/sierpinski-closed-partition-lean/blob/406069edac48c4845bbf303ecc83ee9ef000b99a/Solution.lean#L277-L295
-- source:
--   https://github.com/Arthur742Ramos/sierpinski-closed-partition-lean/blob/406069edac48c4845bbf303ecc83ee9ef000b99a/Solution.lean#L277-L295

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_Sierpinski_Solution
set_option autoImplicit true
@[expose] public section
public section
open Set
universe u v w
open Sierpinski
variable {X : Type u} [tX : TopologicalSpace X] [t2X : T2Space X]

theorem Sierpinski.continuous_choice_eq_one [cX : CompactSpace X] [connX : ConnectedSpace X]
    {Y : Type v} [tY : TopologicalSpace Y] [t2Y : T2Space Y]
    {ι : Type w} [countI : Countable ι] (f : ι → X → Y) (g : X → Y)
    (hf : ∀ i, Continuous (f i)) (hg : Continuous g)
    (hdistinct : ∀ x, Pairwise (fun i j => f i x ≠ f j x))
    (hchoice : ∀ x, ∃ i, g x = f i x) : ∃ i, g = f i := by sorry
