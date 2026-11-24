-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_qmap_injective
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.qmap_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:30.891922+00:00
-- url     : https://prove2.me/theorems/a4d48e79-444a-42d3-8025-e8937abf6a8f
-- title:
--   Geo: qmap injective
-- statement:
--   The Geo construction uses the qmap injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodB.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodB.lean#L15-L15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.Geo.qmap_injective : Function.Injective (qmap : MvPolynomial σ ℤ → MvPolynomial σ ℚ) := by sorry
