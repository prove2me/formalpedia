-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_detD_const_mul
-- name    : PositivityTheory.Rg.Sw.LVs.dp_detD_const_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:08.645867+00:00
-- url     : https://prove2.me/theorems/95d113c6-36d3-5aad-b3c5-7c5d971cfb7b
-- title:
--   LVs: dp det D const mul
-- statement:
--   The LVs construction uses the dp det D const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L23-L32

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
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PositivityTheory.Rg.Sw.LVs.dp_detD_const_mul (c : ℂ) {F : Matrix ι ι ℂ → ℂ} (hF : ContDiffAt ℂ (Fintype.card ι) F 0) :
    detD (fun T => c * F T) = c * detD F := by sorry
