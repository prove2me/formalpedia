-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_iteratedFDeriv_mul_const_of
-- name    : PositivityTheory.Rg.Sw.LVs.iteratedFDeriv_mul_const_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:03.728447+00:00
-- url     : https://prove2.me/theorems/24c34aca-f1b7-47f1-9f3f-b002ca5a3bc4
-- title:
--   LVs: iterated FDeriv mul const of
-- statement:
--   The LVs construction uses the iterated FDeriv mul const of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L157-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L157-L164

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.iteratedFDeriv_mul_const_of (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (c : ℂ)
    (x : M2 n) (hx : x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F y * c) x v = iteratedFDeriv ℂ N F x v * c := by sorry
