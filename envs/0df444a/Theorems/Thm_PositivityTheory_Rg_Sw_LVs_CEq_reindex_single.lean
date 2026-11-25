-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_reindex_single
-- name    : PositivityTheory.Rg.Sw.LVs.CEq.reindex_single
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:35.407344+00:00
-- url     : https://prove2.me/theorems/9b04b456-96fd-4051-a1a7-664b1c02a901
-- title:
--   CEq: reindex single
-- statement:
--   The CEq construction uses the reindex single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L62-L65

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]

theorem PositivityTheory.Rg.Sw.LVs.CEq.reindex_single [DecidableEq ι] [DecidableEq κ] (e' : ι ≃ κ) (a b : ι) :
    (Matrix.single a b (1 : ℂ)).reindex e' e' = Matrix.single (e' a) (e' b) 1 := by sorry
