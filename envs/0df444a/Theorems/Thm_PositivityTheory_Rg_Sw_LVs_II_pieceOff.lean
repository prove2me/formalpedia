-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_pieceOff
-- name    : PositivityTheory.Rg.Sw.LVs.II.pieceOff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:49:19.240783+00:00
-- url     : https://prove2.me/theorems/75589604-5e34-4995-a205-25385ae95fe9
-- title:
--   II: piece Off
-- statement:
--   The II construction uses the piece Off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L107-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L107-L132

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.II.pieceOff (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (c : ℂ) (i j : Fin n) (hij : i ≠ j) :
    fderiv ℂ Θ x (Pij c i j * x) = lam (Pij c i j) * Θ x := by sorry
