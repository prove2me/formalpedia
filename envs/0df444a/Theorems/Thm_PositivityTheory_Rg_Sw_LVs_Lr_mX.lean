-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_Lr_mX
-- name    : PositivityTheory.Rg.Sw.LVs.Lr_mX
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:53.999278+00:00
-- url     : https://prove2.me/theorems/f289cfb6-5597-4f01-a79e-71d75d5da0f5
-- title:
--   LVs: Lr m X
-- statement:
--   The LVs construction uses the Lr m X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L294-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L294-L332

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

theorem PositivityTheory.Rg.Sw.LVs.Lr_mX (Q R : Matrix (Fin n) (Fin n) ℂ) :
    (Lr n * mX 1 Q R 1 : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) = Matrix.fromCols (1 - Q) (Complex.I • (1 + Q)) := by sorry
