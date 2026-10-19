-- Prove2me | Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_exists_kazhdanPair_on_exact_sourceAmbientSymmetricGenerators
-- name    : SoficGroups.KunExactActualSourceAmbientGenerators.exists_kazhdanPair_on_exact_sourceAmbientSymmetricGenerators
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/bba32bd2-ce7a-4e49-88a7-4f3b1b88caef
-- title:
--   SoficGroups.KunExactActualSourceAmbientGenerators.exists_kazhdanPair_on_exact_sourceAmbientSymmetricGenerators
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunExactKazhdanGeneratorChange

theorem SoficGroups.KunExactActualSourceAmbientGenerators.exists_kazhdanPair_on_exact_sourceAmbientSymmetricGenerators
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hgeneratesΓ :
      Subgroup.closure
        (SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤)
    [SoficGroups.HasPropertyT.{0, 0}
      (SoficGroups.prefixElementaryGroup
        SoficGroups.ninePrefixCode)] :
    ∃ P : SoficGroups.KazhdanPair.{0, 0}
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode),
      P.generators = sourceAmbientSymmetricGenerators SΓ := by sorry
