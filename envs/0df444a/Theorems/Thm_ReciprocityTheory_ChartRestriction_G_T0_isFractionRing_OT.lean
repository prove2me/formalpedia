-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_isFractionRing_OT
-- name    : ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_OT
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:31.002293+00:00
-- url     : https://prove2.me/theorems/44a386c7-9589-5569-80df-aff22f423137
-- title:
--   T0: is Fraction Ring OT
-- statement:
--   The T0 construction uses the is Fraction Ring OT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L17-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L17-L49

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

theorem ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_OT :
    letI := algOTKT (K := K) D N
    IsFractionRing (OT K D N) (KTf K D N) := by sorry
