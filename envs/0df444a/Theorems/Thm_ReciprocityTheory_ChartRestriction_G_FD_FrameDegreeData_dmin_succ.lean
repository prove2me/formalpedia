-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_dmin_succ
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.dmin_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:55.767615+00:00
-- url     : https://prove2.me/theorems/4d6bef0b-292e-4b32-864a-735f33bdcaf5
-- title:
--   Frame Degree Data: dmin succ
-- statement:
--   The Frame Degree Data construction uses the dmin succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ProdCastLESucc.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ProdCastLESucc.lean#L72-L75

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.dmin_succ {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    dmin X.Gm x τ k.succ = dmin X.Gm x τ k.castSucc * dOf X x τ k := by sorry
