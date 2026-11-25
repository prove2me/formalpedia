-- Prove2me | Theorems.Thm_Sierpinski_exists_eq_univ_of_nat_closed_partition
-- name    : Sierpinski.exists_eq_univ_of_nat_closed_partition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:53:41.677891+00:00
-- url     : https://prove2.me/theorems/46617a47-6dde-51e9-8099-731473616689
-- title:
--   Sierpinski: exists eq univ of nat closed partition
-- statement:
--   Sierpiński's closed-partition theorem for a nonempty compact connected
--   Hausdorff space. Empty pieces are permitted.
--
--   Source: https://github.com/Arthur742Ramos/sierpinski-closed-partition-lean/blob/406069edac48c4845bbf303ecc83ee9ef000b99a/Solution.lean#L183-L218
-- source:
--   https://github.com/Arthur742Ramos/sierpinski-closed-partition-lean/blob/406069edac48c4845bbf303ecc83ee9ef000b99a/Solution.lean#L183-L218

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

theorem Sierpinski.exists_eq_univ_of_nat_closed_partition
    [cX : CompactSpace X] [connX : ConnectedSpace X]
    (F : ℕ → Set X) (hclosed : ∀ n, IsClosed (F n))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ n, F n = univ) : ∃ n, F n = univ := by sorry
