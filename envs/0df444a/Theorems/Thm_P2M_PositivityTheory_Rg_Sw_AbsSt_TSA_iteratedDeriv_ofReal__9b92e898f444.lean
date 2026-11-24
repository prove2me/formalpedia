-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_AbsSt_TSA_iteratedDeriv_ofReal__9b92e898f444
-- name    : P2M_PositivityTheory_Rg_Sw_AbsSt_TSA_iteratedDeriv_ofReal__9b92e898f444
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:27.396839+00:00
-- url     : https://prove2.me/theorems/3a29d240-e386-4f74-8289-887eb2c97920
-- title:
--   P2 M Positivity Theory Rg Sw Abs St TSA iterated Deriv of Real  9b92e898f444: P2 M Positivity Theory Rg Sw Abs St TSA iterated Deriv of Real  9b92e898f444
-- statement:
--   The P2 M Positivity Theory Rg Sw Abs St TSA iterated Deriv of Real  9b92e898f444 construction uses the P2 M Positivity Theory Rg Sw Abs St TSA iterated Deriv of Real  9b92e898f444 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/IteratedDerivOfReal.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/IteratedDerivOfReal.lean#L7-L23

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_IteratedDerivOfReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.TSA

theorem P2M_PositivityTheory_Rg_Sw_AbsSt_TSA_iteratedDeriv_ofReal__9b92e898f444 {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {h : ℝ → ℂ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hFh : ∀ x : ℝ, F x = h x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧ ∀ x : ℝ, iteratedDeriv p F x = iteratedDeriv p h x := by sorry

alias «PositivityTheory».«Rg».«Sw».«AbsSt».«TSA».«iteratedDeriv_ofReal'» := P2M_PositivityTheory_Rg_Sw_AbsSt_TSA_iteratedDeriv_ofReal__9b92e898f444
