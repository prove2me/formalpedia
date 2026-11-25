-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_pieceN
-- name    : PositivityTheory.Rg.Sw.LVs.II.pieceN
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:01.820939+00:00
-- url     : https://prove2.me/theorems/c7d7e674-359a-4b77-972a-bdac36503618
-- title:
--   II: piece N
-- statement:
--   The II construction uses the piece N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L87-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L87-L103

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

theorem PositivityTheory.Rg.Sw.LVs.II.pieceN (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (β : Matrix (Fin n) (Fin n) ℂ) (hβ : βᴴ = β) :
    fderiv ℂ Θ x (fromBlocks 0 β 0 0 * x) = lam (fromBlocks 0 β 0 0) * Θ x := by sorry
