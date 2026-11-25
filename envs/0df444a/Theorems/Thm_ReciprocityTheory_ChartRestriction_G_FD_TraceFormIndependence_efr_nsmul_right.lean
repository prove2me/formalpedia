-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_efr_nsmul_right
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.efr_nsmul_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:24.261661+00:00
-- url     : https://prove2.me/theorems/1a0d40c5-43bf-4db8-81c6-6b87616366db
-- title:
--   Trace Form Independence: efr nsmul right
-- statement:
--   The Trace Form Independence construction uses the efr nsmul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L90-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L90-L105

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

theorem ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.efr_nsmul_right (X : Data E r) (n : ℕ) (v w : X.Ψ → Fin r → ℂ) :
    efr X v ((n : ℂ) • w) = n * efr X v w := by sorry
