-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_cc_mul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.cc_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:56.977812+00:00
-- url     : https://prove2.me/theorems/cee4c686-7a45-4a56-9209-bb012a9f4a04
-- title:
--   FD: cc mul
-- statement:
--   The FD construction uses the cc mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsIntegralCc.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsIntegralCc.lean#L16-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.cc_mul (x y : E) : cc (x * y) = cc x * cc y := by sorry
