-- Prove2me | Theorems.Thm_PIW_FdPA_fourierJacobi_differentiable
-- name    : PIW.FdPA.fourierJacobi_differentiable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:53.095576+00:00
-- url     : https://prove2.me/theorems/05a20cb2-30d9-437d-bbb7-1e78713c84e0
-- title:
--   Fd PA: fourier Jacobi differentiable
-- statement:
--   The Fd PA construction uses the fourier Jacobi differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/FourierJacobiDifferentiable.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/FourierJacobiDifferentiable.lean#L10-L12

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_FourierJacobiDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
noncomputable section

theorem PIW.FdPA.fourierJacobi_differentiable {E : Type} [Field E] [NumberField E] [IsCMField E] : FjDiff E := by sorry
