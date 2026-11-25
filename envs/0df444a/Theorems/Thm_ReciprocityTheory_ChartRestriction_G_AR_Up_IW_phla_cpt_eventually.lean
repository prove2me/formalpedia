-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_phla_cpt_eventually
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.IW.phla_cpt_eventually
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:27:46.140807+00:00
-- url     : https://prove2.me/theorems/11a65f67-6b78-4cf5-a5d5-ac271980fcac
-- title:
--   IW: phla cpt eventually
-- statement:
--   The IW construction uses the phla cpt eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/InterpStatementPfH.lean#L231-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/InterpStatementPfH.lean#L231-L235

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.IW.phla_cpt_eventually (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) (la : Wt X.Ψ r) :
    (fun w => phla X la (cpt X x0 w)) =ᶠ[𝓝 z]
      fun w => ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Lm X (cpt X x0 w) τ i.succ - Lm X (cpt X x0 w) τ i.castSucc) := by sorry
