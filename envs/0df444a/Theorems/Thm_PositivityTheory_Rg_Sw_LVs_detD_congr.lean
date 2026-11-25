-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_detD_congr
-- name    : PositivityTheory.Rg.Sw.LVs.detD_congr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:28.557861+00:00
-- url     : https://prove2.me/theorems/164eb0a8-26cb-5adb-8589-54215a9f83ed
-- title:
--   LVs: det D congr
-- statement:
--   The LVs construction uses the det D congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L19-L21

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

theorem PositivityTheory.Rg.Sw.LVs.detD_congr {F G : Matrix ι ι ℂ → ℂ} (h : F =ᶠ[nhds 0] G) : detD F = detD G := by sorry
