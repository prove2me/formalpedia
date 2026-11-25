-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_mem_07ce8f9f59e2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_mem_07ce8f9f59e2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:19.739129+00:00
-- url     : https://prove2.me/theorems/17baa9f8-91e6-4e96-a922-4ceecdddb265
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman quot Proj smul iota mem 07ce8f9f59e2: P2 M Ground Theory Heights  Heights Kleiman quot Proj smul iota mem 07ce8f9f59e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman quot Proj smul iota mem 07ce8f9f59e2 construction uses the P2 M Ground Theory Heights  Heights Kleiman quot Proj smul iota mem 07ce8f9f59e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L367-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L367-L373

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
variable {M₁ M₂}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_mem_07ce8f9f59e2 (r : Poly S N) {e : ℤ} (g : M₁.piece e) (c : ℤ) :
    quotProj M₁ M₂ c (r • quotIota M₁ M₂ e g) ∈ Submodule.span (Poly S N) {quotIota M₁ M₂ e g} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«quotProj_smul_iota_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_mem_07ce8f9f59e2
