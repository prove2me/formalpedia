-- Prove2me | Theorems.Thm_ValiantBorder_gridProjections
-- name    : ValiantBorder.gridProjections
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:15:02.452865+00:00
-- url     : https://prove2.me/theorems/ab574e58-0acf-4b6d-9e93-dd97ac88f888
-- title:
--   Hamiltonian cycles and permanents represent grid sums
-- statement:
--   Over every field the directed Hamiltonian cycle family is grid-complete with factor 40. Over each field of characteristic different from two the permanent is grid-complete with factor 3. Thus any grid sum with $t$ incidences is an affine projection of these families for sizes at least $40t$ and $3t$, respectively.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/HcGrid.lean#L64).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/HcGrid.lean#L64. Permanent projection: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Grids.lean#L59.

import Definitions.Def_VP_VNP_all_fields
import Definitions.Def_ValiantBorder_gridComplete

theorem ValiantBorder.gridProjections (K : Type) [Field K] :
    ValiantBorder.GridComplete K (Statement.hc K) 40 ∧
      ((2 : K) ≠ 0 → ValiantBorder.GridComplete K (Statement.perm K) 3) := by sorry
