-- Prove2me | Theorems.Thm_TunnellMap_sqrtBSAux_spec
-- name    : TunnellMap.sqrtBSAux_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:33.448682+00:00
-- url     : https://prove2.me/theorems/510b55e2-d089-5deb-8de6-62e20fe4311f
-- title:
--   Tunnell Map: sqrt BSAux spec
-- statement:
--   The Tunnell Map construction uses the sqrt BSAux spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L45-L73
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L45-L73

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.sqrtBSAux_spec (n : ℕ) :
    ∀ fuel lo hi, lo < hi → hi ≤ lo + 1 + fuel → lo * lo ≤ n → n < hi * hi →
      (sqrtBSAux n fuel lo hi) * (sqrtBSAux n fuel lo hi) ≤ n ∧
        n < (sqrtBSAux n fuel lo hi + 1) * (sqrtBSAux n fuel lo hi + 1) := by sorry
