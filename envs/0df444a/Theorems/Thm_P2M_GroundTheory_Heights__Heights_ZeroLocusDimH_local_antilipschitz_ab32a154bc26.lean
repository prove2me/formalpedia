-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_local_antilipschitz_ab32a154bc26
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_local_antilipschitz_ab32a154bc26
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:43.887927+00:00
-- url     : https://prove2.me/theorems/e404d837-ac93-4ec1-8dcf-b23294421bb1
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H local antilipschitz ab32a154bc26: P2 M Ground Theory Heights  Heights Zero Locus Dim H local antilipschitz ab32a154bc26
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H local antilipschitz ab32a154bc26 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H local antilipschitz ab32a154bc26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L134-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L134-L169

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_local_antilipschitz_ab32a154bc26 {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ)
    (P : Fin n → Polynomial (MvPolynomial (Fin r) ℂ)) (V : Set (Fin n → ℂ))
    (hV : ∀ x ∈ V, ∀ i, Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0)
    (x₀ : Fin n → ℂ)
    (hx₀ : ∀ i, Polynomial.eval (x₀ i)
      ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x₀))) ≠ 0) :
    ∃ U ∈ 𝓝 x₀, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ V ∩ U, ∀ x' ∈ V ∩ U, ‖x - x'‖ ≤ K * ‖paramMap π x - paramMap π x'‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«local_antilipschitz» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_local_antilipschitz_ab32a154bc26
