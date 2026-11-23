-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__pt_cc9506f6e8c7
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__pt_cc9506f6e8c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:53.606575+00:00
-- url     : https://prove2.me/theorems/95e2ccae-65b5-45e2-803c-aa6475f12071
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Trivial Biextension pt  pt cc9506f6e8c7: P2 M Global Theory Indefinite Row Side Full Hecke Trivial Biextension pt  pt cc9506f6e8c7
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Trivial Biextension pt  pt cc9506f6e8c7 construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Trivial Biextension pt  pt cc9506f6e8c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/TrivialBiextension.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/TrivialBiextension.lean#L117-L119

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

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__pt_cc9506f6e8c7 {T : Over S} (a b c : T ⟶ G) (p q : G3 G ⟶ G) :
    pt₃ G a b c ≫ pt G p q = pt G (lift a (lift b c) ≫ p) (lift a (lift b c) ≫ q) := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«TrivialBiextension».«pt₃_pt» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__pt_cc9506f6e8c7
