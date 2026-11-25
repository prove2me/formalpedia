-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___isGen_8ccbc68b0b48
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___isGen_8ccbc68b0b48
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:43.796209+00:00
-- url     : https://prove2.me/theorems/99a33749-9f1f-472c-9457-6a0eea4891f9
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg   is Gen 8ccbc68b0b48: P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg   is
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg   is Gen 8ccbc68b0b48 construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg   is Gen 8ccbc68b0b48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L288-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L288-L323

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
variable (R : Type) [CommRing R] [IsDomain R]
attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite
open GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
variable {R} (D : RawDeg R)

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___isGen_8ccbc68b0b48 (χ χ' : D.X) : (D.τ χ χ').IsGen := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«CompleteLocalNormalRings».«RawDeg».«τ_isGen» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___isGen_8ccbc68b0b48
