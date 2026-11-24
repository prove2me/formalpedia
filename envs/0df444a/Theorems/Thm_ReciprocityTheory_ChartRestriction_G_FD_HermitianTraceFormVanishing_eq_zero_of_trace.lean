-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_eq_zero_of_trace
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.eq_zero_of_trace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:51.397823+00:00
-- url     : https://prove2.me/theorems/ea808cf2-9008-4a0e-b07e-e9139fc8d3a6
-- title:
--   Hermitian Trace Form Vanishing: eq zero of trace
-- statement:
--   The Hermitian Trace Form Vanishing construction uses the eq zero of trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianTraceFormVanishing.lean#L99-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianTraceFormVanishing.lean#L99-L117

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Lemmata_GeneralBFactAltForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.eq_zero_of_trace (a : E) (h : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * a) = 0) :
    a = 0 := by sorry
