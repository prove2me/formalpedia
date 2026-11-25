-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CechDR_cmpZZ___409c8b0dc1df
-- name    : P2M_GlobalTheory_CechDR_cmpZZ___409c8b0dc1df
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:34.895138+00:00
-- url     : https://prove2.me/theorems/da23989a-0638-55e2-9332-5f10a93e3ea3
-- title:
--   P2 M Global Theory Cech DR cmp ZZ   409c8b0dc1df: P2 M Global Theory Cech DR cmp ZZ   409c8b0dc1df
-- statement:
--   The P2 M Global Theory Cech DR cmp ZZ   409c8b0dc1df construction uses the P2 M Global Theory Cech DR cmp ZZ   409c8b0dc1df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ComparisonMemCechHodgeFiltration.lean#L234-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ComparisonMemCechHodgeFiltration.lean#L234-L235

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
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
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh Cris
universe v u v' u'
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem P2M_GlobalTheory_CechDR_cmpZZ___409c8b0dc1df (s : X ⟶ Sp R) (f : Z1 (O (dp0 R) s)) (U : AffOp X) :
    (cmpZZ s f).1.2 U = connForm f (affPt s U.unop) (affPt_w s U.unop) := by sorry

alias «GlobalTheory».«CechDR».«cmpZZ_ω» := P2M_GlobalTheory_CechDR_cmpZZ___409c8b0dc1df
