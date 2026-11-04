-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_Procs_meets
-- name    : ThreeSum.LightTernaryRequesterMatrix.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:50:00.45625+00:00
-- url     : https://prove2.me/theorems/229ba7cb-91d5-4c2f-9ec0-3cd24901e166
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L193-L240
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L193-L240

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryCarryApply_meets
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalRequester_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightTernaryRequesterMatrix.Procs.meets {main : ℕ} (S : Procs P main)
    {src n U J radix carry Q positions matrix work : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+5<lim.depth)
    (hb : 1<radix) (hQ : 0<Q)
    (hsrc : src+n≤positions) (hcarry : carry+Q*(J+1)≤positions)
    (hpos : positions+n*Q≤matrix) (hmat : matrix+n*Q*(J+2)≤work)
    (hspace : LightTernarySignedRow.space work (3*U)≤lim.space)
    (hword : (LightTernarySignedRow.word (3*U) radix J : ℤ)≤lim.word)
    (hread : ∀a<n, μ (src+a)=f a) (hvalues : ∀a<n, |f a|≤(U : ℤ))
    (hCarries : LightTernaryCarryCodes.Table μ carry J Q) :
    Meets lim P main depth [src,n,U,J,radix,carry,Q,positions,matrix,work] μ
      (time n Q J U)
      (fun _ ν => Entries ν positions matrix J Q (n*Q) U radix f ∧ Kept μ ν positions) := by sorry
