-- Prove2me | Theorems.Thm_SoficGroups_KunUnconditionalActualSourceGeneratorData_exists_unconditional_actual_source_generator_data
-- name    : SoficGroups.KunUnconditionalActualSourceGeneratorData.exists_unconditional_actual_source_generator_data
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/62562bfe-ca6a-441d-a827-b8f0387366e3
-- title:
--   SoficGroups.KunUnconditionalActualSourceGeneratorData.exists_unconditional_actual_source_generator_data
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUnconditionalActualSourceGeneratorData
open SoficGroups.KunExactKazhdanGeneratorChange
open SoficGroups.KunExactActualSourceAmbientGenerators

theorem SoficGroups.KunUnconditionalActualSourceGeneratorData.exists_unconditional_actual_source_generator_data :
    ∃ (SΓ : Finset
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))
      (PΓ : SoficGroups.KazhdanPair.{0, 0}
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaPrefixCode))
      (PG : SoficGroups.KazhdanPair.{0, 0}
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode)),
      1 ∈ SΓ ∧
      (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
      Subgroup.closure
        (SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤ ∧
      PΓ.generators = SΓ ∧
      1 ∈ sourceAmbientSymmetricGenerators SΓ ∧
      (∀ g ∈ sourceAmbientSymmetricGenerators SΓ,
        g⁻¹ ∈ sourceAmbientSymmetricGenerators SΓ) ∧
      Subgroup.closure
        (sourceAmbientSymmetricGenerators SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.ninePrefixCode)) = ⊤ ∧
      PG.generators = sourceAmbientSymmetricGenerators SΓ ∧
      Function.Injective sourceAlphaInclusion ∧
      Subgroup.closure
        (Set.range (sourcePositiveGeneratorMap SΓ)) = ⊤ := by sorry
