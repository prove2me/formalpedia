-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SchwartzBaire_iteratedFDeriv_sub_apply__4bfc50ada7a9
-- name    : P2M_GlobalTheory_CompanionTheory_SchwartzBaire_iteratedFDeriv_sub_apply__4bfc50ada7a9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:46.960112+00:00
-- url     : https://prove2.me/theorems/c19c5360-f6ad-41d7-a4f6-f25951cb1df9
-- title:
--   P2 M Global Theory Companion Theory Schwartz Baire iterated FDeriv sub apply  4bfc50ada7a9: P2 M Global Theory Companion Theory Schwartz Baire iterated FDeriv sub apply  4bfc50ada7a9
-- statement:
--   The P2 M Global Theory Companion Theory Schwartz Baire iterated FDeriv sub apply  4bfc50ada7a9 construction uses the P2 M Global Theory Companion Theory Schwartz Baire iterated FDeriv sub apply  4bfc50ada7a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedFDerivSubApply.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedFDerivSubApply.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff Topology Uniformity
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchwartzBaire
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem P2M_GlobalTheory_CompanionTheory_SchwartzBaire_iteratedFDeriv_sub_apply__4bfc50ada7a9 (f g : 𝓢(E, F)) (l : ℕ) (x : E) :
    iteratedFDeriv ℝ l (⇑(f - g)) x = iteratedFDeriv ℝ l f x - iteratedFDeriv ℝ l g x := by sorry

alias «GlobalTheory».«CompanionTheory».«SchwartzBaire».«iteratedFDeriv_sub_apply'» := P2M_GlobalTheory_CompanionTheory_SchwartzBaire_iteratedFDeriv_sub_apply__4bfc50ada7a9
