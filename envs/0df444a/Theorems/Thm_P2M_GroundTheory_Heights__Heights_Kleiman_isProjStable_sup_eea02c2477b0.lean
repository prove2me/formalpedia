-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isProjStable_sup_eea02c2477b0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isProjStable_sup_eea02c2477b0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:55.965449+00:00
-- url     : https://prove2.me/theorems/f4a9a9c4-e585-4a28-b798-13840cd5f71e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Proj Stable sup eea02c2477b0: P2 M Ground Theory Heights  Heights Kleiman is Proj Stable sup eea02c2477b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Proj Stable sup eea02c2477b0 construction uses the P2 M Ground Theory Heights  Heights Kleiman is Proj Stable sup eea02c2477b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L385-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L385-L393

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isProjStable_sup_eea02c2477b0 {A : Submodule (Poly S N) (quotLaurent M₁ M₂)} (hA : IsProjStable M₁ M₂ A)
    {e : ℤ} (g : M₁.piece e) :
    IsProjStable M₁ M₂ (A ⊔ Submodule.span (Poly S N) {quotIota M₁ M₂ e g}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isProjStable_sup» := P2M_GroundTheory_Heights__Heights_Kleiman_isProjStable_sup_eea02c2477b0
