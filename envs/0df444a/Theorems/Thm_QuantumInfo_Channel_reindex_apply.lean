-- Prove2me | Theorems.Thm_QuantumInfo_Channel_reindex_apply
-- name    : QuantumInfo.Channel.reindex_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:39.188558+00:00
-- url     : https://prove2.me/theorems/c4caf954-3cb8-4466-996e-9ea26f487514
-- title:
--   Channel: reindex apply
-- statement:
--   Relabelling the Kraus operators does not change the channel's action.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/Basic.lean#L47-L49
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/Basic.lean#L47-L49

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Definitions.Def_KnillLaflammeLean_Basic
set_option autoImplicit false
@[expose] public section
public section
open Matrix
open QuantumInfo
open QuantumInfo.Channel
variable {n m ι κ : Type*} [Fintype n] [Fintype m] [Fintype ι] [Fintype κ] [DecidableEq n]

theorem QuantumInfo.Channel.reindex_apply (e : ι ≃ κ) (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    (Φ.reindex e).apply ρ = Φ.apply ρ := by sorry
