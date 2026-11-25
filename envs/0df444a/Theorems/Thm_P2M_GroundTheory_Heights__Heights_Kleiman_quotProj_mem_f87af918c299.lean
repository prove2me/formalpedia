-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mem_f87af918c299
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mem_f87af918c299
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:12.820982+00:00
-- url     : https://prove2.me/theorems/f6c6e463-3673-443b-af4f-9d06c6296a84
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman quot Proj mem f87af918c299: P2 M Ground Theory Heights  Heights Kleiman quot Proj mem f87af918c299
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman quot Proj mem f87af918c299 construction uses the P2 M Ground Theory Heights  Heights Kleiman quot Proj mem f87af918c299 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L201-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L201-L203

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
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
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mem_f87af918c299 (c : ℤ) (y : quotLaurent M₁ M₂) : quotProj M₁ M₂ c y ∈ quotPiece M₁ M₂ c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«quotProj_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mem_f87af918c299
