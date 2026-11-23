-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_OpToKT_injective
-- name    : ReciprocityTheory.ChartRestriction.G.T0.OpToKT_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:24.244807+00:00
-- url     : https://prove2.me/theorems/2ac7e9a8-77dd-4d32-a4ff-67cc4db155d0
-- title:
--   T0: Op To KT injective
-- statement:
--   The T0 construction uses the Op To KT injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L65-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)

theorem ReciprocityTheory.ChartRestriction.G.T0.OpToKT_injective (la : HeightOneSpectrum (𝓞 K)) : Function.Injective (OpToKT D N la) := by sorry
