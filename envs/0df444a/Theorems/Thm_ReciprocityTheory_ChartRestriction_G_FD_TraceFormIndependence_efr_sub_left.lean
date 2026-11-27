-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_efr_sub_left
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.efr_sub_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:25.028699+00:00
-- url     : https://prove2.me/theorems/64ebe744-f337-4474-8e05-1f747b5a3def
-- title:
--   Trace Form Independence: efr sub left
-- statement:
--   The Trace Form Independence construction uses the efr sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L83-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.efr_sub_left (X : Data E r) (v v' w : X.Ψ → Fin r → ℂ) :
    efr X (v - v') w = efr X v w - efr X v' w := by sorry
