-- Prove2me | Theorems.Thm_P2M_GlobalTheory__SpecIso_inv_germ_residue_residueFieldMap_f91a5e7af468
-- name    : P2M_GlobalTheory__SpecIso_inv_germ_residue_residueFieldMap_f91a5e7af468
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:39.348441+00:00
-- url     : https://prove2.me/theorems/735acf11-125f-48c8-b5f9-7498527ef717
-- title:
--   P2 M Global Theory  Spec Iso inv germ residue residue Field Map f91a5e7af468: P2 M Global Theory  Spec Iso inv germ residue residue Field Map f91a5e7af468
-- statement:
--   The P2 M Global Theory  Spec Iso inv germ residue residue Field Map f91a5e7af468 construction uses the P2 M Global Theory  Spec Iso inv germ residue residue Field Map f91a5e7af468 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldIsoInvCompSpec.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldIsoInvCompSpec.lean#L32-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory

theorem P2M_GlobalTheory__SpecIso_inv_germ_residue_residueFieldMap_f91a5e7af468 {R B : CommRingCat.{0}} (φ : R ⟶ B) (x : Spec B) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (Spec.map φ x) trivial ≫
        (Spec R).residue (Spec.map φ x) ≫ (Spec.map φ).residueFieldMap x =
      φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ x trivial ≫ (Spec B).residue x := by sorry

alias «GlobalTheory».«ΓSpecIso_inv_germ_residue_residueFieldMap» := P2M_GlobalTheory__SpecIso_inv_germ_residue_residueFieldMap_f91a5e7af468
