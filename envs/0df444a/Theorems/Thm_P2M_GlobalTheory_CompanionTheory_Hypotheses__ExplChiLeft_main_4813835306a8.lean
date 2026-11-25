-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_main_4813835306a8
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_main_4813835306a8
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:49.227431+00:00
-- url     : https://prove2.me/theorems/39b14a2d-dcdd-5a32-b431-7b0a3f449c73
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Expl Chi Left main 4813835306a8: P2 M Global Theory Companion Theory Hypotheses  Expl Chi Left main 4813835306a8
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Expl Chi Left main 4813835306a8 construction uses the P2 M Global Theory Companion Theory Hypotheses  Expl Chi Left main 4813835306a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DirichletLogDerivBoundLeftHalfPlane.lean#L29-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DirichletLogDerivBoundLeftHalfPlane.lean#L29-L155

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivReflectionFormulaStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivBoundLeftHalfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_main_4813835306a8 : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N →
    χ.IsPrimitive → ∀ s : ℂ, s.re ≤ -(1/2 : ℝ) →
    (1 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -((k : ℝ) + 1/2)) →
    DirichletCharacter.LFunction χ s ≠ 0 ∧
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      ≤ C * Real.log (N * (‖s‖ + 2)) := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«ExplChiLeft».«main» := P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_main_4813835306a8
