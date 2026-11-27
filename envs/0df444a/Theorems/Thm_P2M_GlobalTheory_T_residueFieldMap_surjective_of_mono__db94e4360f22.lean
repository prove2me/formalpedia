-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_residueFieldMap_surjective_of_mono__db94e4360f22
-- name    : P2M_GlobalTheory_T_residueFieldMap_surjective_of_mono__db94e4360f22
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:36.577919+00:00
-- url     : https://prove2.me/theorems/ca4745d9-ca74-4f32-b50b-ddb13d74f827
-- title:
--   P2 M Global Theory T residue Field Map surjective of mono  db94e4360f22: P2 M Global Theory T residue Field Map surjective of mono  db94e4360f22
-- statement:
--   The P2 M Global Theory T residue Field Map surjective of mono  db94e4360f22 construction uses the P2 M Global Theory T residue Field Map surjective of mono  db94e4360f22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFieldMapSurjectiveOfMonoStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFieldMapSurjectiveOfMonoStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldMapSurjectiveOfMono
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldMapSurjectiveOfMonoStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_residueFieldMap_surjective_of_mono__db94e4360f22 : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X), Function.Surjective (f.residueFieldMap x).hom := by sorry

alias «GlobalTheory».«T».«residueFieldMap_surjective_of_mono'» := P2M_GlobalTheory_T_residueFieldMap_surjective_of_mono__db94e4360f22
