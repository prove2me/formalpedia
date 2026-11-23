-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AffineQuotient___toQuot_f55bcab7a372
-- name    : P2M_GlobalTheory_AffineQuotient___toQuot_f55bcab7a372
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:23.387903+00:00
-- url     : https://prove2.me/theorems/60f0529c-3d5f-490b-8d5a-abe3b3e95b46
-- title:
--   P2 M Global Theory Affine Quotient   to Quot f55bcab7a372: P2 M Global Theory Affine Quotient   to Quot f55bcab7a372
-- statement:
--   The P2 M Global Theory Affine Quotient   to Quot f55bcab7a372 construction uses the P2 M Global Theory Affine Quotient   to Quot f55bcab7a372 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L174-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L174-L183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem P2M_GlobalTheory_AffineQuotient___toQuot_f55bcab7a372 (U : Y.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toQuot f g a ha p hp = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype) ≫
        (cover f g a ha p hp).f U := by sorry

alias «GlobalTheory».«AffineQuotient».«ι_toQuot» := P2M_GlobalTheory_AffineQuotient___toQuot_f55bcab7a372
