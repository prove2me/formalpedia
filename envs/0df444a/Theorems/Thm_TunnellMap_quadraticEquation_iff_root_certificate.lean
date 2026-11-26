-- Prove2me | Theorems.Thm_TunnellMap_quadraticEquation_iff_root_certificate
-- name    : TunnellMap.quadraticEquation_iff_root_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:28.50566+00:00
-- url     : https://prove2.me/theorems/c2889686-47d1-5bb3-8a09-d8506bd95a11
-- title:
--   Tunnell Map: quadratic Equation iff root certificate
-- statement:
--   The Tunnell Map construction uses the quadratic Equation iff root certificate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L18-L39
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L18-L39

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.quadraticEquation_iff_root_certificate {α c d a : ℤ} (hα : α ≠ 0) :
    quadraticEquation α c d a ↔
      ∃ u : ℤ, u ^ 2 = quadraticHalfDiscriminant α c d ∧ α * a = -c + u := by sorry
