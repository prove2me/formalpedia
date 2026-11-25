-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_minor_gt
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.minor_gt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:20:51.05443+00:00
-- url     : https://prove2.me/theorems/31d1e3bc-4cf5-5ab4-81c5-217c7ffae894
-- title:
--   Orthonormal Chart Bounds: minor gt
-- statement:
--   The Orthonormal Chart Bounds construction uses the minor gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SignTypeCancelIdentity.lean#L127-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SignTypeCancelIdentity.lean#L127-L174

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.minor_gt {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (k : ℕ) (hk : k ≤ r - X.p0) (i : Fin (r + 1)) (hik : (i : ℕ) = X.p0 + k) :
    0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by sorry
