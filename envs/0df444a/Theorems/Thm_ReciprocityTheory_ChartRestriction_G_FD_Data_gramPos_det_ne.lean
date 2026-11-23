-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_det_ne
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.gramPos_det_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:41.804355+00:00
-- url     : https://prove2.me/theorems/ed09a0b0-fa5a-4a0d-94a9-667026261d39
-- title:
--   Data: gram Pos det ne
-- statement:
--   The Data construction uses the gram Pos det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatMulVec.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatMulVec.lean#L112-L117

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.gramPos_det_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : (X.gramPos x τ).det ≠ 0 := by sorry
