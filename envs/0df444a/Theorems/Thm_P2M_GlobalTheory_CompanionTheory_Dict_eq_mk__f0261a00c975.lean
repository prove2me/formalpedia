-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Dict_eq_mk__f0261a00c975
-- name    : P2M_GlobalTheory_CompanionTheory_Dict_eq_mk__f0261a00c975
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:51:12.059544+00:00
-- url     : https://prove2.me/theorems/196224f8-5014-5db0-98e0-ef2268e3a828
-- title:
--   P2 M Global Theory Companion Theory Dict eq mk  f0261a00c975: P2 M Global Theory Companion Theory Dict eq mk  f0261a00c975
-- statement:
--   The P2 M Global Theory Companion Theory Dict eq mk  f0261a00c975 construction uses the P2 M Global Theory Companion Theory Dict eq mk  f0261a00c975 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L86-L90

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dict
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem P2M_GlobalTheory_CompanionTheory_Dict_eq_mk__f0261a00c975 (c : ComposableArrows C 2) (x : c.obj' 0 ⟶ c.obj' 1) (y : c.obj' 1 ⟶ c.obj' 2)
    (hx : map' c 0 1 = x) (hy : map' c 1 2 = y) : c = mk₂ x y := by sorry

alias «GlobalTheory».«CompanionTheory».«Dict».«eq_mk₂» := P2M_GlobalTheory_CompanionTheory_Dict_eq_mk__f0261a00c975
