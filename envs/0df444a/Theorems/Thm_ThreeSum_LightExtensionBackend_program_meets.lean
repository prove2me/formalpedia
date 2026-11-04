-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionBackend_program_meets
-- name    : ThreeSum.LightExtensionBackend.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:40:26.232697+00:00
-- url     : https://prove2.me/theorems/f6c68c42-6506-4e60-aae2-3de964dbe5ea
-- title:
--   Light Extension Backend: program meets
-- statement:
--   The Light Extension Backend construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackend.lean#L64-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackend.lean#L64-L145

import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuSemantics
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightExtensionBackend
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
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
noncomputable section
open ThreeSum ThreeSum.LightExtensionBackend
open Light TernaryExtensionEncoding
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
attribute [local instance] ThreeSum.LightExtensionBackend._p2m_local_instance_a49b488cb7_11
variable {lim : Limits}

theorem ThreeSum.LightExtensionBackend.program_meets (F : LightExtensionFactorPredicate.Layout) [Fact F.p.Prime]
    {q fctx ctx table logical physical J a b h r prod sum T depth : ℕ}
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+13 < lim.depth)
    (B : Budget lim F q fctx ctx table logical physical J a b h r prod sum T)
    (hq : q=F.p^F.dim) :
    Meets lim program 37 depth
      [F.p,F.dim,q,F.powers,F.target,fctx,F.left,F.right,ctx,table,logical,physical,a,b,h,r,prod,sum,J]
      μ (time F q J a b h r prod sum T)
      (fun z ν => ∃ c < q, z=(c+1 : ℕ) ∧ Irreducible (monicOfCode (p := F.p) F.dim c) ∧
        (∀ s < q*q, ∀ i < J+2, ν (physical+s*(J+2)+i)=
          (LightExtensionSeedMatrix.value (encodedMul (modulusMonic F c)) q F.p s
            (TernarySignedLayout.offset J i) : ℤ)) ∧ Kept μ ν F.powers) := by sorry
