-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__law___18ce999fa2e8
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__law___18ce999fa2e8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:12.462153+00:00
-- url     : https://prove2.me/theorems/18c96573-3a94-403b-ba36-fcce7791cf46
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Trivial Biextension pt  law   18ce999fa2e8: P2 M Global Theory Indefinite Row Side Full Hecke Trivial Biextension pt  law   18ce999fa2e8
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Trivial Biextension pt  law   18ce999fa2e8 construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Trivial Biextension pt  law   18ce999fa2e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/TrivialBiextension.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/TrivialBiextension.lean#L127-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__law___18ce999fa2e8 {T : Over S} (a b b' : T ⟶ G) :
    (fun k => pt₃ G a b b' ≫ law₂φ G (x3 G 0) (x3 G 1) (x3 G 2) k) = law₂φ G a b b' := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«TrivialBiextension».«pt₃_law₂φ» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__law___18ce999fa2e8
