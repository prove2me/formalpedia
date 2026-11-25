-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TransvectionPeriodicity_cR_neg
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.cR_neg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:14:31.165506+00:00
-- url     : https://prove2.me/theorems/a001e2e7-244f-5bf6-a7bc-f11cf0b3ee4d
-- title:
--   Transvection Periodicity: c R neg
-- statement:
--   The Transvection Periodicity construction uses the c R neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TransvectionPeriodicity.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TransvectionPeriodicity.lean#L153-L155

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.cR_neg (p : X.Ψ → ℝ) : cR X (-p) = -cR X p := by sorry
