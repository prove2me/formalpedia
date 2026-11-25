-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_bound_right_960b4eaa5826
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_bound_right_960b4eaa5826
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:01.512068+00:00
-- url     : https://prove2.me/theorems/9464f411-c931-4e46-b087-2f8e210071e3
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Expl Chi Left bound right 960b4eaa5826: P2 M Global Theory Companion Theory Hypotheses  Expl Chi Left bound right 960b4eaa5826
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Expl Chi Left bound right 960b4eaa5826 construction uses the P2 M Global Theory Companion Theory Hypotheses  Expl Chi Left bound right 960b4eaa5826 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DirichletLogDerivBoundLeftHalfPlane.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DirichletLogDerivBoundLeftHalfPlane.lean#L11-L27

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_bound_right_960b4eaa5826 : ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ), 3 / 2 ≤ s.re → ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ B := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«ExplChiLeft».«bound_right» := P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_bound_right_960b4eaa5826
