-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_exists_simple_root_data_bdff81d3faa4
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_exists_simple_root_data_bdff81d3faa4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:32.001807+00:00
-- url     : https://prove2.me/theorems/baac949a-0d9b-4aae-a9bd-f2d0f388355e
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H exists simple root data bdff81d3faa4: P2 M Ground Theory Heights  Heights Zero Locus Dim H exists simple root data bdff81d3faa4
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H exists simple root data bdff81d3faa4 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H exists simple root data bdff81d3faa4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHAlg.lean#L44-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHAlg.lean#L44-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_exists_simple_root_data_bdff81d3faa4 {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [hp : p.IsPrime] :
    ∃ s : ℕ, (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ∧
    ∃ (π : Fin s → MvPolynomial (Fin n) ℂ) (P : Fin n → Polynomial (MvPolynomial (Fin s) ℂ)),
      (∀ i, (P i).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∈ p) ∧
      (∀ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∉ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«exists_simple_root_data» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_exists_simple_root_data_bdff81d3faa4
