-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbCoh_Wedge_wedgeMap__Multi_7d41d1d54b99
-- name    : P2M_GlobalTheory_AbCoh_Wedge_wedgeMap__Multi_7d41d1d54b99
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:23:32.629458+00:00
-- url     : https://prove2.me/theorems/93a78742-9255-4f0f-b00c-ed2c407070f9
-- title:
--   P2 M Global Theory Ab Coh Wedge wedge Map  Multi 7d41d1d54b99: P2 M Global Theory Ab Coh Wedge wedge Map  Multi 7d41d1d54b99
-- statement:
--   The P2 M Global Theory Ab Coh Wedge wedge Map  Multi 7d41d1d54b99 construction uses the P2 M Global Theory Ab Coh Wedge wedge Map  Multi 7d41d1d54b99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WedgePropertyFromFibres.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WedgePropertyFromFibres.lean#L75-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WedgePropertyFromFibres
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.Wedge
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

theorem P2M_GlobalTheory_AbCoh_Wedge_wedgeMap__Multi_7d41d1d54b99 (hsq : ∀ x : HO1 s, cup _ x x = 0) (v : Fin 2 → HO1 s) :
    wedgeMap s hsq (exteriorPower.ιMulti R 2 v) = cup _ (v 0) (v 1) := by sorry

alias «GlobalTheory».«AbCoh».«Wedge».«wedgeMap_ιMulti» := P2M_GlobalTheory_AbCoh_Wedge_wedgeMap__Multi_7d41d1d54b99
