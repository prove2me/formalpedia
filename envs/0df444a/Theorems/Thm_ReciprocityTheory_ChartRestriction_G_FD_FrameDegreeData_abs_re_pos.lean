-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_abs_re_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.abs_re_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:05.581706+00:00
-- url     : https://prove2.me/theorems/6f474bce-abd0-4fe0-911c-af9fde32cfa6
-- title:
--   Frame Degree Data: abs re pos
-- statement:
--   The Frame Degree Data construction uses the abs re pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ProdCastLESucc.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ProdCastLESucc.lean#L99-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.abs_re_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : 0 < |(dOf X x τ k).re| := by sorry
