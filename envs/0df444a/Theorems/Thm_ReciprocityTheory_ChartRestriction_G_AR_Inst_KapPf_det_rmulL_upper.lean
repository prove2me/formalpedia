-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_det_rmulL_upper
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.det_rmulL_upper
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:56:14.554916+00:00
-- url     : https://prove2.me/theorems/ebf995da-169b-43fd-8c5d-5fc425b33568
-- title:
--   Kap Pf: det rmul L upper
-- statement:
--   The Kap Pf construction uses the det rmul L upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DetOfBlockDiag.lean#L155-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DetOfBlockDiag.lean#L155-L170

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.det_rmulL_upper (b : Frame X.Ψ r) (hup : ∀ τ a x, x < a → b τ a x = 0) :
    LinearMap.det (rmulL X b) = ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 := by sorry
