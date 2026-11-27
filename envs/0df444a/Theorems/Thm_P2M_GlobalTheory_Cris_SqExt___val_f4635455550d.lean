-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Cris_SqExt___val_f4635455550d
-- name    : P2M_GlobalTheory_Cris_SqExt___val_f4635455550d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:57.713588+00:00
-- url     : https://prove2.me/theorems/01b87056-3f81-5094-b465-287ab636ed88
-- title:
--   P2 M Global Theory Cris Sq Ext   val f4635455550d: P2 M Global Theory Cris Sq Ext   val f4635455550d
-- statement:
--   The P2 M Global Theory Cris Sq Ext   val f4635455550d construction uses the P2 M Global Theory Cris Sq Ext   val f4635455550d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L608-L633
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L608-L633

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
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
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {X X' X'' : Scheme.{0}}
attribute [instance] Thick.ring Thick.alg Thick.ring₀
attribute [instance] SqExt.ringC SqExt.ringB SqExt.algC SqExt.algB
open GlobalTheory.Cris.SqExt
variable {s : X ⟶ Sp R} (E E' : SqExt R)

theorem P2M_GlobalTheory_Cris_SqExt___val_f4635455550d (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) (f : Form s) :
    E.π (E.val y hy f.1) = 0 := by sorry

alias «GlobalTheory».«Cris».«SqExt».«π_val» := P2M_GlobalTheory_Cris_SqExt___val_f4635455550d
