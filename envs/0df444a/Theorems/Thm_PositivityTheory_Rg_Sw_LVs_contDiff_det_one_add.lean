-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiff_det_one_add
-- name    : PositivityTheory.Rg.Sw.LVs.contDiff_det_one_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:40.49577+00:00
-- url     : https://prove2.me/theorems/a921999e-d5b4-4866-a4ed-3953d0f4b0da
-- title:
--   LVs: cont Diff det one add
-- statement:
--   The LVs construction uses the cont Diff det one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L34-L44

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

theorem PositivityTheory.Rg.Sw.LVs.contDiff_det_one_add (M : Matrix ι ι ℂ) {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun S : Matrix ι ι ℂ => (1 + M * S).det) := by sorry
