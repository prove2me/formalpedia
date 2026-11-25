-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_SublatticeCoefficients_ioc_orth
-- name    : ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients.ioc_orth
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:54.485883+00:00
-- url     : https://prove2.me/theorems/405522bf-6d51-4df4-a354-d1bfde43762e
-- title:
--   Sublattice Coefficients: ioc orth
-- statement:
--   The Sublattice Coefficients construction uses the ioc orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SublatticeCoefficients.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SublatticeCoefficients.lean#L10-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SublatticeCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
open NumberField Complex MeasureTheory ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
  ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing

theorem ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients.ioc_orth (m : ℤ) :
    ∫ t in Set.Ioc (0 : ℝ) 1, cexp (2 * Real.pi * I * (m : ℂ) * (t : ℂ)) = if m = 0 then 1 else 0 := by sorry
