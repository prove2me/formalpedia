-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H__equiv__naturality_4575878c8334
-- name    : P2M_GroundTheory_Arith_SchemeCoh_H__equiv__naturality_4575878c8334
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:24.52801+00:00
-- url     : https://prove2.me/theorems/9f8ee0e9-d47d-4679-87dd-c112e3afffea
-- title:
--   P2 M Ground Theory Arith Scheme Coh H  equiv  naturality 4575878c8334: P2 M Ground Theory Arith Scheme Coh H  equiv  naturality 4575878c8334
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh H  equiv  naturality 4575878c8334 construction uses the P2 M Ground Theory Arith Scheme Coh H  equiv  naturality 4575878c8334 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L126-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L126-L139

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

theorem P2M_GroundTheory_Arith_SchemeCoh_H__equiv__naturality_4575878c8334 {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (U : C)
    (x : F.H' 0 U) :
    H'.equiv₀ G U (((Sheaf.cohomologyPresheafFunctor J 0).map φ).app (op U) x) =
      φ.hom.app (op U) (H'.equiv₀ F U x) := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«H'».«equiv₀_naturality» := P2M_GroundTheory_Arith_SchemeCoh_H__equiv__naturality_4575878c8334
