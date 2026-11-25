-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_nsq_mulVec_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.nsq_mulVec_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:56.176771+00:00
-- url     : https://prove2.me/theorems/1899f891-baec-4b11-9f3a-06b29da0d3c5
-- title:
--   Orthonormal Chart Bounds: nsq mul Vec le
-- statement:
--   The Orthonormal Chart Bounds construction uses the nsq mul Vec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/NsqMulVecLeOpN.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/NsqMulVecLeOpN.lean#L16-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NsqMulVecLeOpN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.nsq_mulVec_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (A.mulVec v) ≤ (∑ i, ∑ j, ‖A i j‖ ^ 2) * nsq v := by sorry
