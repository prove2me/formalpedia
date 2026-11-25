-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_Ck_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.Ck_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:23.196558+00:00
-- url     : https://prove2.me/theorems/5071a9df-bf1a-5122-be50-21ab3736b4e5
-- title:
--   Curv Pf: Ck eq
-- statement:
--   The Curv Pf construction uses the Ck eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/TelePoint.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/TelePoint.lean#L13-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviLogfk
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_TelePoint
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.Ck_eq (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (k : Fin (r + 1)) :
    Ck X b z u τ k = ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < k ∧ (k : ℕ) ≤ j then
      (Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2) else 0 := by sorry
