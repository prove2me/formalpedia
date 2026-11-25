-- Prove2me | Theorems.Thm_Research_triPoint_injective
-- name    : Research.triPoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:07:03.468149+00:00
-- url     : https://prove2.me/theorems/07b7c5b9-0534-53fc-bd09-b999587085aa
-- title:
--   Research: tri Point injective
-- statement:
--   Triangular-lattice integer coordinates represent distinct planar points.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L157-L170
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L157-L170

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells
set_option autoImplicit true
@[expose] public section
public section
open Research

theorem Research.triPoint_injective : Function.Injective triPoint := by sorry
