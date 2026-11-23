-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_integer_smul_eq_coe_smul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.integer_smul_eq_coe_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:18.817642+00:00
-- url     : https://prove2.me/theorems/4640368e-0d83-4ee6-958c-9ef380741f53
-- title:
--   FD: integer smul eq coe smul
-- statement:
--   The FD construction uses the integer smul eq coe smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermEqZeroOfTraceFormVanish.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermEqZeroOfTraceFormVanish.lean#L12-L15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.integer_smul_eq_coe_smul {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := by sorry
