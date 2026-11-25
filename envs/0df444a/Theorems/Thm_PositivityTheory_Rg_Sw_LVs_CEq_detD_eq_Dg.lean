-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_detD_eq_Dg
-- name    : PositivityTheory.Rg.Sw.LVs.CEq.detD_eq_Dg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:25.480231+00:00
-- url     : https://prove2.me/theorems/207f90ed-fc29-4f1c-a083-dc9946c0e30c
-- title:
--   CEq: det D eq Dg
-- statement:
--   The CEq construction uses the det D eq Dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L45-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L45-L45

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
omit [DecidableEq ι]

theorem PositivityTheory.Rg.Sw.LVs.CEq.detD_eq_Dg (F : Matrix κ κ ℂ → ℂ) : detD F = Dg (Fintype.equivFin κ) F := by sorry
