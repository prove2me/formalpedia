-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_Procs_inner_meets
-- name    : ThreeSum.LightTernaryRequesterMatrix.Procs.inner_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:18.815955+00:00
-- url     : https://prove2.me/theorems/832cdf42-4fed-434f-abf6-6d91f493794a
-- title:
--   Procs: inner meets
-- statement:
--   The Procs construction uses the inner meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L64-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L64-L184

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightTernaryRequesterMatrix.Procs.inner_meets {main : ℕ} (S : Procs P main)
    {src n U J radix carry Q positions matrix work i : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+4<lim.depth)
    (hb : 1<radix) (hQ : 0<Q) (hi : i<n)
    (hsrc : src+n≤positions) (hcarry : carry+Q*(J+1)≤positions)
    (hpos : positions+n*Q≤matrix) (hmat : matrix+n*Q*(J+2)≤work)
    (hspace : LightTernarySignedRow.space work (3*U)≤lim.space)
    (hword : (LightTernarySignedRow.word (3*U) radix J : ℤ)≤lim.word)
    (hread : ∀a<n, μ (src+a)=f a) (hvalues : ∀a<n, |f a|≤(U : ℤ))
    (hCarries : LightTernaryCarryCodes.Table μ carry J Q)
    (hOld : Entries μ positions matrix J Q (i*Q) U radix f) :
    Meets lim P S.inner depth [src,U,J,radix,carry,Q,positions,matrix,work,i] μ
      (innerTime Q J U)
      (fun _ ν => Entries ν positions matrix J Q ((i+1)*Q) U radix f ∧ Kept μ ν positions) := by sorry
