-- Prove2me | Theorems.Thm_SZ_continuum_le_mk_witnessSet
-- name    : SZ.continuum_le_mk_witnessSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:40:33.801897+00:00
-- url     : https://prove2.me/theorems/413559bd-89fe-463a-869c-370c9aec44f6
-- title:
--   SZ: continuum le mk witness Set
-- statement:
--   **Theorem 9.1, cardinality half.**  The witness set has the cardinality of the
--   continuum — already inside `[4/3, 5/3]`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1180-L1187
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1180-L1187

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.continuum_le_mk_witnessSet :
    Cardinal.continuum ≤ Cardinal.mk witnessSet := by sorry
