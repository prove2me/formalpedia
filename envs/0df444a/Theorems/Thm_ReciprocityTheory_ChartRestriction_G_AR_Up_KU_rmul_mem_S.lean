-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_rmul_mem_S
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.KU.rmul_mem_S
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:09:42.132478+00:00
-- url     : https://prove2.me/theorems/0ace6999-71f8-4bc0-8475-29d732389021
-- title:
--   KU: rmul mem S
-- statement:
--   The KU construction uses the rmul mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfC.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfC.lean#L129-L140

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instMSMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instBorelMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instSCMat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instPolishFrame

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.KU.rmul_mem_S (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ Sset X x0 FF ↔ y ∈ Sset X x0 FF := by sorry
