-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_SublatticeCoefficients_cube_orth
-- name    : ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients.cube_orth
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:27.779523+00:00
-- url     : https://prove2.me/theorems/32a7a73c-2b70-406f-9080-44112614acf0
-- title:
--   Sublattice Coefficients: cube orth
-- statement:
--   The Sublattice Coefficients construction uses the cube orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SublatticeCoefficients.lean#L26-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SublatticeCoefficients.lean#L26-L44

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

theorem ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients.cube_orth {n : ℕ} (m : Fin n → ℤ) :
    ∫ t in Set.univ.pi (fun _ : Fin n => Set.Ioc (0 : ℝ) 1),
      cexp (2 * Real.pi * I * ∑ j, (m j : ℂ) * (t j : ℂ)) = if m = 0 then 1 else 0 := by sorry
