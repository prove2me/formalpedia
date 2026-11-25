-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_faithfullyFlat_app_of_isAffineHom_flat_surjective__ca00d372e8df
-- name    : P2M_GlobalTheory_T_faithfullyFlat_app_of_isAffineHom_flat_surjective__ca00d372e8df
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:31.195687+00:00
-- url     : https://prove2.me/theorems/e77b9642-c52c-519d-a47d-f79f22d837dd
-- title:
--   P2 M Global Theory T faithfully Flat app of is Affine Hom flat surjective  ca00d372e8df: P2 M Global Theory T faithfully Flat app of is Affine Hom flat surjective  ca00d372e8df
-- statement:
--   The P2 M Global Theory T faithfully Flat app of is Affine Hom flat surjective  ca00d372e8df construction uses the P2 M Global Theory T faithfully Flat app of is Affine Hom flat surjective  ca00d372e8df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FaithfullyFlatAppOfIsAffineHomFlatSurjectiveStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FaithfullyFlatAppOfIsAffineHomFlatSurjectiveStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FaithfullyFlatAppOfIsAffineHomFlatSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FaithfullyFlatAppOfIsAffineHomFlatSurjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_faithfullyFlat_app_of_isAffineHom_flat_surjective__ca00d372e8df : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p → IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by sorry

alias «GlobalTheory».«T».«faithfullyFlat_app_of_isAffineHom_flat_surjective'» := P2M_GlobalTheory_T_faithfullyFlat_app_of_isAffineHom_flat_surjective__ca00d372e8df
