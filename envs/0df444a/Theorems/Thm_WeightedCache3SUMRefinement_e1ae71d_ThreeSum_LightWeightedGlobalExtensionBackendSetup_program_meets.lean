-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalExtensionBackendSetup_program_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalExtensionBackendSetup.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:21:05.059026+00:00
-- url     : https://prove2.me/theorems/f62ab790-1c2b-4f75-aa5a-52fb68d4aee2
-- title:
--   program_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightExtensionBackendSetup.lean#L49-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightExtensionBackendSetup.lean#L49-L136

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightExtensionBackendSetup
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionBackend_program_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorSearch_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalExtensionBackendSetup
open Light TernaryExtensionEncoding LightExtensionBackendLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {depth : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalExtensionBackendSetup.program_meets {base d p q J : ℕ} [Fact p.Prime]
    (μ : ℕ → ℤ) (hdim : 0 < d) (hq : p^d=q)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+14 < lim.depth)
    (hspace : base+reserve d p q J ≤ lim.space) :
    Meets lim program 38 depth [p,d,q,J,base] μ (time base d p q J)
      (fun z ν => ∃ c < q, z=(c+1 : ℕ) ∧ Irreducible (monicOfCode (p := p) d c) ∧
        (∀ s < q*q, ∀ i < J+2, ν (physical base d q J+s*(J+2)+i)=
          (LightExtensionSeedMatrix.value
            (encodedMul (LightExtensionBackend.modulusMonic (factor base d p q J) c)) q p s
            (TernarySignedLayout.offset J i) : ℤ)) ∧ Kept μ ν base) := by sorry
