-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_of_mem_862f94617fb4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_of_mem_862f94617fb4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:16:14.139486+00:00
-- url     : https://prove2.me/theorems/606761d4-2175-43ab-ae63-059b948a7941
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Restrict Gen resid of mem 862f94617fb4: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Restrict Gen resid
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Restrict Gen resid of mem 862f94617fb4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Restrict Gen resid of mem 862f94617fb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ResidOfMem.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ResidOfMem.lean#L21-L21

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_of_mem_862f94617fb4 {a : Ω} (h : a ∈ R) : RestrictGen.resid R σ a = σ ⟨a, h⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«RestrictGen».«resid_of_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_of_mem_862f94617fb4
