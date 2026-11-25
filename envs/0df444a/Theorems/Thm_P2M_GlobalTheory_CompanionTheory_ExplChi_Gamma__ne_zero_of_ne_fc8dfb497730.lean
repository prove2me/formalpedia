-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_ExplChi_Gamma__ne_zero_of_ne_fc8dfb497730
-- name    : P2M_GlobalTheory_CompanionTheory_ExplChi_Gamma__ne_zero_of_ne_fc8dfb497730
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:03:40.766305+00:00
-- url     : https://prove2.me/theorems/a08c7824-91d8-48b4-833f-8d35572f2214
-- title:
--   P2 M Global Theory Companion Theory Expl Chi Gamma  ne zero of ne fc8dfb497730: P2 M Global Theory Companion Theory Expl Chi Gamma  ne zero of ne fc8dfb497730
-- statement:
--   The P2 M Global Theory Companion Theory Expl Chi Gamma  ne zero of ne fc8dfb497730 construction uses the P2 M Global Theory Companion Theory Expl Chi Gamma  ne zero of ne fc8dfb497730 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DirichletLogDerivReflectionFormula.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DirichletLogDerivReflectionFormula.lean#L29-L32

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivReflectionFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplChi
open Complex DirichletCharacter

theorem P2M_GlobalTheory_CompanionTheory_ExplChi_Gamma__ne_zero_of_ne_fc8dfb497730 {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) : Gammaℝ z ≠ 0 := by sorry

alias «GlobalTheory».«CompanionTheory».«ExplChi».«Gammaℝ_ne_zero_of_ne» := P2M_GlobalTheory_CompanionTheory_ExplChi_Gamma__ne_zero_of_ne_fc8dfb497730
