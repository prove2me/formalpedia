-- Prove2me | Theorems.Thm_Sierpinski_exists_eq_univ_of_countable_closed_partition
-- name    : Sierpinski.exists_eq_univ_of_countable_closed_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:53:51.152075+00:00
-- url     : https://prove2.me/theorems/59674fb7-2bf6-5d6e-8809-8ab70cf3c6ab
-- title:
--   Sierpinski: exists eq univ of countable closed partition
-- statement:
--   Any countable closed partition of a continuum has a piece equal to the
--   whole space. This includes finite index types and allows empty pieces.
--
--   Source: https://github.com/Arthur742Ramos/sierpinski-closed-partition-lean/blob/406069edac48c4845bbf303ecc83ee9ef000b99a/Solution.lean#L222-L273
-- source:
--   https://github.com/Arthur742Ramos/sierpinski-closed-partition-lean/blob/406069edac48c4845bbf303ecc83ee9ef000b99a/Solution.lean#L222-L273

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

theorem Sierpinski.exists_eq_univ_of_countable_closed_partition
    [cX : CompactSpace X] [connX : ConnectedSpace X] {ι : Type v} [countI : Countable ι]
    (F : ι → Set X) (hclosed : ∀ i, IsClosed (F i))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ i, F i = univ) : ∃ i, F i = univ := by sorry
