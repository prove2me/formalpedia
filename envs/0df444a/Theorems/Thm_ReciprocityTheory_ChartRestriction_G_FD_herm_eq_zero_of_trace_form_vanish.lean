-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_herm_eq_zero_of_trace_form_vanish
-- name    : ReciprocityTheory.ChartRestriction.G.FD.herm_eq_zero_of_trace_form_vanish
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:11.443796+00:00
-- url     : https://prove2.me/theorems/9f811bcd-cfac-5117-a887-46d7930eca4c
-- title:
--   FD: herm eq zero of trace form vanish
-- statement:
--   The FD construction uses the herm eq zero of trace form vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermEqZeroOfTraceFormVanish.lean#L27-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermEqZeroOfTraceFormVanish.lean#L27-L57

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

theorem ReciprocityTheory.ChartRestriction.G.FD.herm_eq_zero_of_trace_form_vanish {r : ℕ} (ξ0 : E) (hξ0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (x y : Fin r → E) (h : ∀ β : 𝓞 E, EFf ξ0 G x (β • y) = 0) : herm G x y = 0 := by sorry
