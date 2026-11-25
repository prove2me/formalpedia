-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_ExplChi_hasDerivAt_Gamma__of_ne_8141e52e745e
-- name    : P2M_GlobalTheory_CompanionTheory_ExplChi_hasDerivAt_Gamma__of_ne_8141e52e745e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:03:45.662232+00:00
-- url     : https://prove2.me/theorems/ead00ce7-3f37-4c18-9e49-e6ea1472e59a
-- title:
--   P2 M Global Theory Companion Theory Expl Chi has Deriv At Gamma  of ne 8141e52e745e: P2 M Global Theory Companion Theory Expl Chi has Deriv At Gamma  of ne 8141e52e745e
-- statement:
--   The P2 M Global Theory Companion Theory Expl Chi has Deriv At Gamma  of ne 8141e52e745e construction uses the P2 M Global Theory Companion Theory Expl Chi has Deriv At Gamma  of ne 8141e52e745e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DirichletLogDerivReflectionFormula.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DirichletLogDerivReflectionFormula.lean#L7-L27

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

theorem P2M_GlobalTheory_CompanionTheory_ExplChi_hasDerivAt_Gamma__of_ne_8141e52e745e {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) :
    HasDerivAt Gammaℝ
      (Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2)) z := by sorry

alias «GlobalTheory».«CompanionTheory».«ExplChi».«hasDerivAt_Gammaℝ_of_ne» := P2M_GlobalTheory_CompanionTheory_ExplChi_hasDerivAt_Gamma__of_ne_8141e52e745e
