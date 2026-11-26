-- Prove2me | Theorems.Thm_TunnellMap_isqrtK_eq
-- name    : TunnellMap.isqrtK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:30.8147+00:00
-- url     : https://prove2.me/theorems/3bf98b15-6cd6-4e8e-ace0-cae2250f31fd
-- title:
--   Tunnell Map: isqrt K eq
-- statement:
--   The Tunnell Map construction uses the isqrt K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L90-L91
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L90-L91

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.isqrtK_eq (z : ℤ) : isqrtK z = Int.sqrt z := by sorry
