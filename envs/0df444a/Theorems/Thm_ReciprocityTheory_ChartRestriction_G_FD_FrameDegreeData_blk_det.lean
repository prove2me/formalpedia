-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_blk_det
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.blk_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:50.986856+00:00
-- url     : https://prove2.me/theorems/7f792785-af20-4b3e-ae56-17cc83cd445c
-- title:
--   Frame Degree Data: blk det
-- statement:
--   The Frame Degree Data construction uses the blk det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ProdCastLESucc.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ProdCastLESucc.lean#L41-L47

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.blk_det {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (c : Fin r) :
    (blk (gram τ.1 X.Gm (mat x τ)) c).det ≠ 0 := by sorry
