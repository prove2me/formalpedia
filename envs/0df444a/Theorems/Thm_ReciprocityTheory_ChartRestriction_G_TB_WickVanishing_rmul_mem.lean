-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_rmul_mem
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.rmul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:13.252923+00:00
-- url     : https://prove2.me/theorems/f48a833e-84a7-538a-8fd8-b6a5581acd41
-- title:
--   Wick Vanishing: rmul mem
-- statement:
--   The Wick Vanishing construction uses the rmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConn.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConn.lean#L44-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.rmul_mem {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ X.dom := by sorry
