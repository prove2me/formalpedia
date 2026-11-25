-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DetPowPairing_coeff_pderiv__dbf7971f6bc0
-- name    : P2M_GlobalTheory_DetPowPairing_coeff_pderiv__dbf7971f6bc0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:16.177739+00:00
-- url     : https://prove2.me/theorems/4b39a769-a149-4302-8881-81b1f1510844
-- title:
--   P2 M Global Theory Det Pow Pairing coeff pderiv  dbf7971f6bc0: P2 M Global Theory Det Pow Pairing coeff pderiv  dbf7971f6bc0
-- statement:
--   The P2 M Global Theory Det Pow Pairing coeff pderiv  dbf7971f6bc0 construction uses the P2 M Global Theory Det Pow Pairing coeff pderiv  dbf7971f6bc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L59-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]

theorem P2M_GlobalTheory_DetPowPairing_coeff_pderiv__dbf7971f6bc0 (j : σ) (A : σ →₀ ℕ) (Q : MvPolynomial σ C) :
    coeff A (pderiv j Q) = coeff (A + Finsupp.single j 1) Q * ((A j : C) + 1) := by sorry

alias «GlobalTheory».«DetPowPairing».«coeff_pderiv'» := P2M_GlobalTheory_DetPowPairing_coeff_pderiv__dbf7971f6bc0
