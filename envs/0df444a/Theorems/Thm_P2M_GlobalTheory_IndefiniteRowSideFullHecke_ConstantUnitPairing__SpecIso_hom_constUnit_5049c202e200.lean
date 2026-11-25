-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_ConstantUnitPairing__SpecIso_hom_constUnit_5049c202e200
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_ConstantUnitPairing__SpecIso_hom_constUnit_5049c202e200
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:23.544454+00:00
-- url     : https://prove2.me/theorems/aded5e74-7dd3-4e30-bbef-f4e28bd8034e
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Constant Unit Pairing  Spec Iso hom const Unit 5049c202e200: P2 M Global Theory Indefinite Row Side Full Hecke Constant Unit Pairing  Spec Iso hom con
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Constant Unit Pairing  Spec Iso hom const Unit 5049c202e200 construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Constant Unit Pairing  Spec Iso hom const Unit 5049c202e200 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/ConstantUnitPairing.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/ConstantUnitPairing.lean#L22-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_ConstantUnitPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_ConstantUnitPairing__SpecIso_hom_constUnit_5049c202e200 (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (ζ : Fˣ) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (constUnit R F ζ : Γ((TFK (R := R) F).left, ⊤)) = (ζ : F) := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«ConstantUnitPairing».«ΓSpecIso_hom_constUnit» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_ConstantUnitPairing__SpecIso_hom_constUnit_5049c202e200
