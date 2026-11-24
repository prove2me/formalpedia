-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_algebraMap_mvPolynomial_int_complex_a208a4dfdd5b
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_algebraMap_mvPolynomial_int_complex_a208a4dfdd5b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:23:40.160808+00:00
-- url     : https://prove2.me/theorems/2a2fd764-a0f9-4058-83e2-c3d5098f3256
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel algebra Map mv Polynomial int complex a208a4dfdd5b: P2 M Ground Theory Heights  Heights Hilbert Samuel algebra Map mv Polynomial int complex a208a4df
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel algebra Map mv Polynomial int complex a208a4dfdd5b construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel algebra Map mv Polynomial int complex a208a4dfdd5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComplexMinimalPrimesContract.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComplexMinimalPrimesContract.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexMinimalPrimesContract
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComplexMinimalPrimesContract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_algebraMap_mvPolynomial_int_complex_a208a4dfdd5b (σ : Type) :
    algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) = MvPolynomial.map (Int.castRingHom ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«algebraMap_mvPolynomial_int_complex» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_algebraMap_mvPolynomial_int_complex_a208a4dfdd5b
