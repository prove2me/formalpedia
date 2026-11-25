-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbCoh__Two_apply_63110fbf2b67
-- name    : P2M_GlobalTheory_AbCoh__Two_apply_63110fbf2b67
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:08:32.615965+00:00
-- url     : https://prove2.me/theorems/9e66e04e-d563-5c15-be89-a558485608b0
-- title:
--   P2 M Global Theory Ab Coh  Two apply 63110fbf2b67: P2 M Global Theory Ab Coh  Two apply 63110fbf2b67
-- statement:
--   The P2 M Global Theory Ab Coh  Two apply 63110fbf2b67 construction uses the P2 M Global Theory Ab Coh  Two apply 63110fbf2b67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2ExteriorSquareIso.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2ExteriorSquareIso.lean#L48-L49

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
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem P2M_GlobalTheory_AbCoh__Two_apply_63110fbf2b67 (a b : M) : ιTwo a b = exteriorPower.ιMulti R 2 ![a, b] := by sorry

alias «GlobalTheory».«AbCoh».«ιTwo_apply» := P2M_GlobalTheory_AbCoh__Two_apply_63110fbf2b67
