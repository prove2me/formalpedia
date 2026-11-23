-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Op_isDVR
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Op_isDVR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:21.602796+00:00
-- url     : https://prove2.me/theorems/cd57d496-f41e-491c-8c4b-2b710a00b9fe
-- title:
--   T0: Op is DVR
-- statement:
--   The T0 construction uses the Op is DVR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OpIsDVR.lean#L7-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OpIsDVR.lean#L7-L86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.Op_isDVR {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (Op D N la) := by sorry
