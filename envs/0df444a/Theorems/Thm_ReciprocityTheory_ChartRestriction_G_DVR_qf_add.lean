-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_qf_add
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.qf_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:14.331937+00:00
-- url     : https://prove2.me/theorems/e463cff1-6b0d-483d-88d3-bfbfbb563591
-- title:
--   DVR: qf add
-- statement:
--   The DVR construction uses the qf add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/QuadTie.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/QuadTie.lean#L11-L12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
variable {𝕜 W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup W] [Module 𝕜 W]
variable {B : LinearMap.BilinForm 𝕜 W}

theorem ReciprocityTheory.ChartRestriction.G.DVR.qf_add (hB : ∀ x y, B x y = B y x) (x y : W) : qf B (x + y) = qf B x + B x y + qf B y := by sorry
