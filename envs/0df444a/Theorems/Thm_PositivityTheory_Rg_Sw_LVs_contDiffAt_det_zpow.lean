-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiffAt_det_zpow
-- name    : PositivityTheory.Rg.Sw.LVs.contDiffAt_det_zpow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:12.041319+00:00
-- url     : https://prove2.me/theorems/2615c326-fb53-5da8-8317-78761809855b
-- title:
--   LVs: cont Diff At det zpow
-- statement:
--   The LVs construction uses the cont Diff At det zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L46-L53

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

theorem PositivityTheory.Rg.Sw.LVs.contDiffAt_det_zpow (M : Matrix ι ι ℂ) (t : ℤ) {k : WithTop ℕ∞} :
    ContDiffAt ℂ k (fun S : Matrix ι ι ℂ => (1 + M * S).det ^ t) 0 := by sorry
