-- Prove2me | Theorems.Thm_P2M_GlobalTheory_MinorNorm_coeff_pderiv__5701bf4a009b
-- name    : P2M_GlobalTheory_MinorNorm_coeff_pderiv__5701bf4a009b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:07.662774+00:00
-- url     : https://prove2.me/theorems/4e1df6d9-cf69-43f5-89da-ac97fc3064c9
-- title:
--   P2 M Global Theory Minor Norm coeff pderiv  5701bf4a009b: P2 M Global Theory Minor Norm coeff pderiv  5701bf4a009b
-- statement:
--   The P2 M Global Theory Minor Norm coeff pderiv  5701bf4a009b construction uses the P2 M Global Theory Minor Norm coeff pderiv  5701bf4a009b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L443-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L443-L460

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {σ : Type}

theorem P2M_GlobalTheory_MinorNorm_coeff_pderiv__5701bf4a009b (v : σ) (m : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    (pderiv v Q).coeff m = Q.coeff (m + Finsupp.single v 1) * (m v + 1) := by sorry

alias «GlobalTheory».«MinorNorm».«coeff_pderiv'» := P2M_GlobalTheory_MinorNorm_coeff_pderiv__5701bf4a009b
