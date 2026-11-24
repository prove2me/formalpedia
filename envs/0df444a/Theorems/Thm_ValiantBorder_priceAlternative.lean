-- Prove2me | Theorems.Thm_ValiantBorder_priceAlternative
-- name    : ValiantBorder.priceAlternative
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:23:33.23943+00:00
-- url     : https://prove2.me/theorems/35170d5f-fef2-4f7e-b625-ba3b141720dc
-- title:
--   Every field is flat or contracting
-- statement:
--   For each field, either every finite Euclidean configuration gives a price, or some binary matrix dimension admits a uniform contraction of the root-mean-square price for full-rank displacements relative to rank-one displacements.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Alternative.lean#L921).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Alternative.lean#L921.

import Definitions.Def_ValiantBorder_fieldCases

theorem ValiantBorder.priceAlternative (K : Type) [Field K] : Paper.Flat K ∨ Paper.Contracting K := by sorry
