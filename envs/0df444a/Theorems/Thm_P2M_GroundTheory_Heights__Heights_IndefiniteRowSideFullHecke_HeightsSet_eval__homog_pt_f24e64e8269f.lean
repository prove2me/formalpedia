-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_eval__homog_pt_f24e64e8269f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_eval__homog_pt_f24e64e8269f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:46.147999+00:00
-- url     : https://prove2.me/theorems/ec5e0e0a-f413-454f-ac38-634f2250a7bc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set eval  homog pt f24e64e8269f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set eval  homog p
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set eval  homog pt f24e64e8269f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set eval  homog pt f24e64e8269f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSaturatedFirstCoordinateLine.lean#L188-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSaturatedFirstCoordinateLine.lean#L188-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open NumberField

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_eval__homog_pt_f24e64e8269f {R : Type*} [CommRing R] (f : ℤ →+* R) (z : (Σ _ : Unit, PBlk 1 ()) → R)
    (g : MRing (PBlk 1)) (d : Unit → ℕ) (hg : IsMultiHomog g d) :
    eval₂ f z g = f (∑ m ∈ g.support, g.coeff m) * z ⟨(), 0⟩ ^ d () := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«eval₂_homog_pt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_eval__homog_pt_f24e64e8269f
