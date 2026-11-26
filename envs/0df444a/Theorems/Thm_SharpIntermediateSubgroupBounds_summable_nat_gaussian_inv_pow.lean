-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_summable_nat_gaussian_inv_pow
-- name    : SharpIntermediateSubgroupBounds.summable_nat_gaussian_inv_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:02.963877+00:00
-- url     : https://prove2.me/theorems/7f392b0c-10fd-49b8-9db0-5f160805b897
-- title:
--   Sharp Intermediate Subgroup Bounds: summable nat gaussian inv pow
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the summable nat gaussian inv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L473-L480
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L473-L480

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.summable_nat_gaussian_inv_pow {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun j : ℕ ↦ (p : ℝ)⁻¹ ^ (j * j)) := by sorry
