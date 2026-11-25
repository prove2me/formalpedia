-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbCoh_sum_sum__Two_of_symm_2966c7908e33
-- name    : P2M_GlobalTheory_AbCoh_sum_sum__Two_of_symm_2966c7908e33
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T17:07:49.135455+00:00
-- url     : https://prove2.me/theorems/98303488-a063-445d-9fec-b49471dedfc1
-- title:
--   P2 M Global Theory Ab Coh sum sum  Two of symm 2966c7908e33: P2 M Global Theory Ab Coh sum sum  Two of symm 2966c7908e33
-- statement:
--   The P2 M Global Theory Ab Coh sum sum  Two of symm 2966c7908e33 construction uses the P2 M Global Theory Ab Coh sum sum  Two of symm 2966c7908e33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2ExteriorSquareIso.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2ExteriorSquareIso.lean#L60-L71

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

theorem P2M_GlobalTheory_AbCoh_sum_sum__Two_of_symm_2966c7908e33 {n : ℕ} (x : Fin n → M) (c : Fin n → Fin n → R)
    (hc : ∀ a b, c a b = c b a) : ∑ a, ∑ b, c a b • ιTwo (R := R) (x a) (x b) = 0 := by sorry

alias «GlobalTheory».«AbCoh».«sum_sum_ιTwo_of_symm» := P2M_GlobalTheory_AbCoh_sum_sum__Two_of_symm_2966c7908e33
