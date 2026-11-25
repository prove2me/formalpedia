-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_exists_mul_pow_eq_mkF_840b0bae13e0
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_exists_mul_pow_eq_mkF_840b0bae13e0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:04.056693+00:00
-- url     : https://prove2.me/theorems/e2a8c377-07f6-42b0-af8a-f723f84b8bf6
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections exists mul pow eq mk F 840b0bae13e0: P2 M Ground Theory Heights  Heights Small Sections exists mul pow eq mk F 840b0bae13e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections exists mul pow eq mk F 840b0bae13e0 construction uses the P2 M Ground Theory Heights  Heights Small Sections exists mul pow eq mk F 840b0bae13e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L88-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L88-L117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
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
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SmallSections_exists_mul_pow_eq_mkF_840b0bae13e0 {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (N : ℕ) (E : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ N = P.mkF E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«exists_mul_pow_eq_mkF» := P2M_GroundTheory_Heights__Heights_SmallSections_exists_mul_pow_eq_mkF_840b0bae13e0
