-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg__At_trans_8cc8ae9ac14b
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg__At_trans_8cc8ae9ac14b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:24.773677+00:00
-- url     : https://prove2.me/theorems/b4ba4e74-92d4-475b-836c-a56a14f9ddf2
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg  At trans 8cc8ae9ac14b: P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg  At
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg  At trans 8cc8ae9ac14b construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Complete Local Normal Rings Raw Deg  At trans 8cc8ae9ac14b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L244-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L244-L254

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

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg__At_trans_8cc8ae9ac14b (χ : D.X) (i i' : D.P.L.ι) {V V' W} (h h') (k : W ≤ V) (k' : W ≤ V') (hW) :
    res k (D.ψAt χ i V h) = (D.gAt (D.cK χ).left i i' W hW)⁻¹ * res k' (D.ψAt χ i' V' h') := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«CompleteLocalNormalRings».«RawDeg».«ψAt_trans» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg__At_trans_8cc8ae9ac14b
