-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___symm_70d81a164892
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___symm_70d81a164892
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:45.358598+00:00
-- url     : https://prove2.me/theorems/f8299289-b907-4e7b-90bc-706500cf9470
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg   symm 70d81a164892: P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg   symm
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg   symm 70d81a164892 construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg   symm 70d81a164892 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L211-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L211-L221

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

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___symm_70d81a164892 (χ χ' : D.X) : LB.Gen.Corr D.P.L _ _ _ _ (D.τ χ χ') (D.τ χ' χ) := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«CompleteLocalNormalRings».«RawDeg».«τ_symm» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___symm_70d81a164892
