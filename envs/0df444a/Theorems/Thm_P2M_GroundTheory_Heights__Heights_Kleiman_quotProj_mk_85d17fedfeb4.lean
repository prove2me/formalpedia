-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mk_85d17fedfeb4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mk_85d17fedfeb4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:44.330899+00:00
-- url     : https://prove2.me/theorems/888677e2-1368-581b-a115-a225abdc2178
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman quot Proj mk 85d17fedfeb4: P2 M Ground Theory Heights  Heights Kleiman quot Proj mk 85d17fedfeb4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman quot Proj mk 85d17fedfeb4 construction uses the P2 M Ground Theory Heights  Heights Kleiman quot Proj mk 85d17fedfeb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L181-L183

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mk_85d17fedfeb4 (c : ℤ) (m : M₁.laurent) :
    quotProj M₁ M₂ c (Submodule.Quotient.mk m) =
      quotIota M₁ M₂ c ⟨(m : LaurentSpace x E) c, m.2 c⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«quotProj_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mk_85d17fedfeb4
