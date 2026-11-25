-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbCoh_cupWedge__Two_1a44d08a1dcd
-- name    : P2M_GlobalTheory_AbCoh_cupWedge__Two_1a44d08a1dcd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:00:00.500309+00:00
-- url     : https://prove2.me/theorems/4e2c1664-d1a4-5df4-943e-5fbdc08c51b5
-- title:
--   P2 M Global Theory Ab Coh cup Wedge  Two 1a44d08a1dcd: P2 M Global Theory Ab Coh cup Wedge  Two 1a44d08a1dcd
-- statement:
--   The P2 M Global Theory Ab Coh cup Wedge  Two 1a44d08a1dcd construction uses the P2 M Global Theory Ab Coh cup Wedge  Two 1a44d08a1dcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2ExteriorSquareIso.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2ExteriorSquareIso.lean#L102-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalOneFormFrameCoordinatesConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumCupOneFormsZeroImpCoordinatesZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CupSumClosedGlobalOneFormsEqZeroIffSumWedgeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2GeneratedByCupsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumWedgeGlobalOneFormsEqZeroIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2ExteriorSquareIso
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem P2M_GlobalTheory_AbCoh_cupWedge__Two_1a44d08a1dcd (halt : ∀ a, cupHyp F a a = 0) (a b : Hyp1 F) :
    cupWedge F halt (ιTwo a b) = cupHyp F a b := by sorry

alias «GlobalTheory».«AbCoh».«cupWedge_ιTwo» := P2M_GlobalTheory_AbCoh_cupWedge__Two_1a44d08a1dcd
