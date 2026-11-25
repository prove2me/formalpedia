-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mvPolynomial_finite_frobenius_range_091c722b10a9
-- name    : P2M_GroundTheory_Heights__Heights_Model_mvPolynomial_finite_frobenius_range_091c722b10a9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:55.921668+00:00
-- url     : https://prove2.me/theorems/d85973a5-d0c3-4ab2-a608-ba6cf7860ad6
-- title:
--   P2 M Ground Theory Heights  Heights Model mv Polynomial finite frobenius range 091c722b10a9: P2 M Ground Theory Heights  Heights Model mv Polynomial finite frobenius range 091c722b10a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mv Polynomial finite frobenius range 091c722b10a9 construction uses the P2 M Ground Theory Heights  Heights Model mv Polynomial finite frobenius range 091c722b10a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharP.lean#L53-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharP.lean#L53-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model

theorem P2M_GroundTheory_Heights__Heights_Model_mvPolynomial_finite_frobenius_range_091c722b10a9 (p : ℕ) [Fact p.Prime] (s e : ℕ) :
    Module.Finite (iterateFrobenius (MvPolynomial (Fin s) (ZMod p)) p e).range
      (MvPolynomial (Fin s) (ZMod p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mvPolynomial_finite_frobenius_range» := P2M_GroundTheory_Heights__Heights_Model_mvPolynomial_finite_frobenius_range_091c722b10a9
