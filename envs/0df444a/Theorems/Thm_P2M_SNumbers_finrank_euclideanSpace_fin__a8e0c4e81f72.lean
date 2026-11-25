-- Prove2me | Theorems.Thm_P2M_SNumbers_finrank_euclideanSpace_fin__a8e0c4e81f72
-- name    : P2M_SNumbers_finrank_euclideanSpace_fin__a8e0c4e81f72
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:13.145836+00:00
-- url     : https://prove2.me/theorems/24da8981-ffff-427d-be3d-f7d96ac858b5
-- title:
--   P2 M SNumbers finrank euclidean Space fin  a8e0c4e81f72: P2 M SNumbers finrank euclidean Space fin  a8e0c4e81f72
-- statement:
--   The dimension of `ℓ₂ⁿ = EuclideanSpace 𝕜 (Fin n)` is `n`, over any
--   `NontriviallyNormedField`. Mathlib's `finrank_euclideanSpace_fin` proves the
--   same, but only for `RCLike` fields; the s-number axioms are stated over a general
--   field, so this variant is what the `(S5)` normalisations `_id_euclidean` need.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/ContinuousLinearMapRank.lean#L90-L93
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/ContinuousLinearMapRank.lean#L90-L93

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open SNumbers
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

theorem P2M_SNumbers_finrank_euclideanSpace_fin__a8e0c4e81f72 (n : ℕ) :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by sorry

alias «SNumbers».«finrank_euclideanSpace_fin'» := P2M_SNumbers_finrank_euclideanSpace_fin__a8e0c4e81f72
