-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inverse_first_block_unipotent_formula
-- name    : PositivityTheory.Rg.Sw.LVs.inverse_first_block_unipotent_formula
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:19.609055+00:00
-- url     : https://prove2.me/theorems/f90f3bde-ce8b-5197-8c01-ff93ed9e441f
-- title:
--   LVs: inverse first block unipotent formula
-- statement:
--   The LVs construction uses the inverse first block unipotent formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L334-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L334-L356

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

theorem PositivityTheory.Rg.Sw.LVs.inverse_first_block_unipotent_formula {x : M2 n} (hx : InG x) (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0) (hRQ : R * Q = 0) :
    ub1 (x * mX 1 Q R 1) = (u1 x)ᴴ + Q * (u2 x)ᴴ := by sorry
