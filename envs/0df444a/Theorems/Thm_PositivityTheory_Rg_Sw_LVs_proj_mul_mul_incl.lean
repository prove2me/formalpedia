-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_proj_mul_mul_incl
-- name    : PositivityTheory.Rg.Sw.LVs.proj_mul_mul_incl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:44.547175+00:00
-- url     : https://prove2.me/theorems/d8121599-9f42-4de1-878c-ce8ebbf5f519
-- title:
--   LVs: proj mul mul incl
-- statement:
--   The LVs construction uses the proj mul mul incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L107-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L107-L111

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

theorem PositivityTheory.Rg.Sw.LVs.proj_mul_mul_incl (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) :
    proj s * M * dp_incl s = M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n)) := by sorry
