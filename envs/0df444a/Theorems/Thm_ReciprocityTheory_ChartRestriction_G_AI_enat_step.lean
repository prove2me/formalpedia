-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_enat_step
-- name    : ReciprocityTheory.ChartRestriction.G.AI.enat_step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:50.421351+00:00
-- url     : https://prove2.me/theorems/8df9aefe-d46e-44ac-898c-de8f3f61454b
-- title:
--   AI: enat step
-- statement:
--   The AI construction uses the enat step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L338-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L338-L365

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v

theorem ReciprocityTheory.ChartRestriction.G.AI.enat_step {k1 k3 c2 k2 c1 c3 s1 s3 : ℕ∞} (h1 : k1 ≠ ⊤) (h3 : k3 ≠ ⊤) (hc1 : c1 ≠ ⊤)
    (hc3 : c3 ≠ ⊤) (hc2 : c2 ≠ ⊤) (e1 : c1 = k1 + s1) (e3 : c3 = k3 + s3)
    (eu : k1 + k3 + c2 = k2 + c1 + c3) : k2 ≠ ⊤ ∧ c2 = k2 + (s1 + s3) := by sorry
