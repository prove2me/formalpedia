-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_two_D_sq_khw
-- name    : ReciprocityTheory.ChartRestriction.DS.two_D_sq_khw
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:19.36708+00:00
-- url     : https://prove2.me/theorems/118ae4a1-9d8e-4e74-a934-b1826392c25c
-- title:
--   DS: two D sq khw
-- statement:
--   The DS construction uses the two D sq khw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L254-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L254-L274

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.two_D_sq_khw {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hC : IsCAR cp cm) (hEC : CommutesCAR E cp cm) {δ : Fin n → ℝ} {v : W}
    (hv : IsKHWVec ε (diagE ε E cp cm) (δ + rhoHol ε) v) {c : ℂ} (hc : casimir E v = c • v) :
    (2 : ℂ) • ((dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm)) v =
      (((nsq (δ + rhoC ε) - nsq (rho n) : ℝ) : ℂ) - c) • v := by sorry
