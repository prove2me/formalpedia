-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_AbsSt_TSA_eq_of_iteratedDeriv
-- name    : PositivityTheory.Rg.Sw.AbsSt.TSA.eq_of_iteratedDeriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:18.283176+00:00
-- url     : https://prove2.me/theorems/3449983b-ae9f-462d-8854-32fff8124f8a
-- title:
--   TSA: eq of iterated Deriv
-- statement:
--   The TSA construction uses the eq of iterated Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/IteratedDerivOfReal.lean#L25-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/IteratedDerivOfReal.lean#L25-L45

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

theorem PositivityTheory.Rg.Sw.AbsSt.TSA.eq_of_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (h : ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0) (t : ℝ) : f t = g t := by sorry
