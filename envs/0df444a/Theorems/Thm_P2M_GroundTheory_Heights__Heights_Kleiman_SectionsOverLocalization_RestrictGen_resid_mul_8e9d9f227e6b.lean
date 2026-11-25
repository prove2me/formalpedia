-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_mul_8e9d9f227e6b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_mul_8e9d9f227e6b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:57:22.602524+00:00
-- url     : https://prove2.me/theorems/ab475347-b0da-462f-a247-04e3fff1a0c2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Restrict Gen resid mul 8e9d9f227e6b: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Restrict Gen resid mu
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Restrict Gen resid mul 8e9d9f227e6b construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Restrict Gen resid mul 8e9d9f227e6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ResidOfMem.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ResidOfMem.lean#L33-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ResidOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {K' : Type} [Field K'] [Algebra F K']
  (R : Subalgebra F Ω) (σ : R →ₐ[F] K')

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_mul_8e9d9f227e6b {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a * b) = RestrictGen.resid R σ a * RestrictGen.resid R σ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«RestrictGen».«resid_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_mul_8e9d9f227e6b
