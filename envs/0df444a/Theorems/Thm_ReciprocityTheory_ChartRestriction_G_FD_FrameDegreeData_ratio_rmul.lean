-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ratio_rmul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ratio_rmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:32.220425+00:00
-- url     : https://prove2.me/theorems/cdfe16df-9780-4686-89c8-a3d1bd7ebd3a
-- title:
--   Frame Degree Data: ratio rmul
-- statement:
--   The Frame Degree Data construction uses the ratio rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthonormalFlagTranslateHolds.lean#L91-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthonormalFlagTranslateHolds.lean#L91-L112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ratio_rmul (x : Frame X.Ψ r) (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (k : Fin r) :
    ‖dmin X.Gm (rmul x b) τ k.succ / dmin X.Gm (rmul x b) τ k.castSucc‖ =
      ‖b τ k k‖ ^ 2 * ‖dmin X.Gm x τ k.succ / dmin X.Gm x τ k.castSucc‖ := by sorry
