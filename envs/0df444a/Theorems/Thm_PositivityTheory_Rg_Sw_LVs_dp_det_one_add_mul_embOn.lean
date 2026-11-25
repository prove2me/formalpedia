-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_det_one_add_mul_embOn
-- name    : PositivityTheory.Rg.Sw.LVs.dp_det_one_add_mul_embOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:38.21854+00:00
-- url     : https://prove2.me/theorems/959cc1bd-5636-4b5b-8cf4-ae3db3c1ff86
-- title:
--   LVs: dp det one add mul emb On
-- statement:
--   The LVs construction uses the dp det one add mul emb On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L113-L117

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.dp_det_one_add_mul_embOn (M : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) (T : Matrix s s ℂ) :
    (1 + M * embOn s T).det =
      (1 + M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n)) * T).det := by sorry
