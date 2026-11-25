-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_span_extend_span_c9691f2c572e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_span_extend_span_c9691f2c572e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:21:26.323386+00:00
-- url     : https://prove2.me/theorems/2cc6da74-570d-457c-bfbf-f85d7b579328
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman span extend span c9691f2c572e: P2 M Ground Theory Heights  Heights Kleiman span extend span c9691f2c572e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman span extend span c9691f2c572e construction uses the P2 M Ground Theory Heights  Heights Kleiman span extend span c9691f2c572e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L43-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
open scoped Pointwise
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_span_extend_span_c9691f2c572e (I : Chart x) (P : Set Ω) :
    Submodule.span (chartRing F x I) (Submodule.span (chartRing S x I) P : Set Ω) =
      Submodule.span (chartRing F x I) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«span_extend_span» := P2M_GroundTheory_Heights__Heights_Kleiman_span_extend_span_c9691f2c572e
