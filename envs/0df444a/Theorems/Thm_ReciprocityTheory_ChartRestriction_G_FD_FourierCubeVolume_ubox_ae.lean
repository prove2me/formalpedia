-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_ubox_ae
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume.ubox_ae
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:48.82535+00:00
-- url     : https://prove2.me/theorems/7883c460-97c5-4a22-90c8-5be563218610
-- title:
--   Fourier Cube Volume: ubox ae
-- statement:
--   The Fourier Cube Volume construction uses the ubox ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCubeVolume.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCubeVolume.lean#L84-L92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume.ubox_ae (N : ℕ) : (I2.DimB.ubox N) =ᵐ[volume] cube N := by sorry
