-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AffineQuotient___fromQuot_2934bbd4beb2
-- name    : P2M_GlobalTheory_AffineQuotient___fromQuot_2934bbd4beb2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:04.798543+00:00
-- url     : https://prove2.me/theorems/1b3333a7-2707-4c36-a37a-a6e9f213e82f
-- title:
--   P2 M Global Theory Affine Quotient   from Quot 2934bbd4beb2: P2 M Global Theory Affine Quotient   from Quot 2934bbd4beb2
-- statement:
--   The P2 M Global Theory Affine Quotient   from Quot 2934bbd4beb2 construction uses the P2 M Global Theory Affine Quotient   from Quot 2934bbd4beb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L188-L191

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

theorem P2M_GlobalTheory_AffineQuotient___fromQuot_2934bbd4beb2 (U : Y.affineOpens) :
    (cover f g a ha p hp).f U ≫ fromQuot f g a ha p hp =
      Spec.map ((diagramMap f g a ha p hp).app (.op U.1)) ≫ U.2.fromSpec := by sorry

alias «GlobalTheory».«AffineQuotient».«ι_fromQuot» := P2M_GlobalTheory_AffineQuotient___fromQuot_2934bbd4beb2
