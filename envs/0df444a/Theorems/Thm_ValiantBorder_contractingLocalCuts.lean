-- Prove2me | Theorems.Thm_ValiantBorder_contractingLocalCuts
-- name    : ValiantBorder.contractingLocalCuts
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:04:03.521337+00:00
-- url     : https://prove2.me/theorems/f3d916bb-d5f7-4955-bb78-8775a7cb1a90
-- title:
--   Contracting fields admit local cut programs
-- statement:
--   Every contracting field contains a subring finitely generated over the integers with a finitely supported assignment of weights for which the single-cut program exists across its prescribed range of parameters.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Cuts.lean#L101).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Cuts.lean#L101.

import Definitions.Def_ValiantBorder_localCuts
import Definitions.Def_ValiantBorder_fieldCases

theorem ValiantBorder.contractingLocalCuts {K : Type} [Field K] (hK : Paper.Contracting K) :
    ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A) (θ : List Bool → A),
      (Function.support θ).Finite ∧ NS1.LocalCuts θ := by sorry
