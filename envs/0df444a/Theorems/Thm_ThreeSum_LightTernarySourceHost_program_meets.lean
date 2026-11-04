-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceHost_program_meets
-- name    : ThreeSum.LightTernarySourceHost.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:42:59.798714+00:00
-- url     : https://prove2.me/theorems/8b03e071-28b0-4fae-9f65-9ce1d8f68f0a
-- title:
--   Light Ternary Source Host: program meets
-- statement:
--   The Light Ternary Source Host construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHost.lean#L47-L264
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHost.lean#L47-L264

import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalJoin
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSources
import Definitions.Def_Submission_ThreeSum_TernarySourceHostRecords
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceHost
open Light RadixKeyLists ThreeSum.LightSubsetAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
variable {lim : Limits}

theorem ThreeSum.LightTernarySourceHost.program_meets (xs ys zs : List ℤ) (hxy : ys.length=xs.length) (hxz : zs.length=xs.length)
    {base0 dst0 base1 dst1 base2 dst2 p0 p1 p2 U0 U1 U2 J d
      src NL M free a bank powers W L keyBase valueBase weightBase weightU factor groups U : ℕ}
    (μ : ℕ → ℤ) (input weight : ℕ → ℤ) (codes key group : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hm : 0<xs.length)
    (hbase0 : base0+xs.length≤dst0)
    (hnext0 : LightRadixKeys.space dst0 xs.length J≤base1)
    (hbase1 : base1+xs.length≤dst1)
    (hnext1 : LightRadixKeys.space dst1 xs.length J≤base2)
    (hbase2 : base2+xs.length≤dst2)
    (hinitEnd : LightRadixKeys.space dst2 xs.length J≤free)
    (hsrc : src+NL≤base0) (hweights : weightBase+NL≤base0)
    (hbank : a+bank≤base0) (hpowerEnd : powers+(W+1)≤base0)
    (hkeyBase : LightWantedSetup.space free M input (dictionary xs p0 J)
      NL (size xs J) U 0 0≤keyBase)
    (hkeyEnd : keyBase+count xs p0 J M NL input≤valueBase)
    (hvalues : valueBase+groups*bank≤lim.space)
    (hb0 : ∀ x∈xs, |x|≤(U0 : ℤ)) (hb1 : ∀ x∈ys, |x|≤(U1 : ℤ))
    (hb2 : ∀ x∈zs, |x|≤(U2 : ℤ))
    (hw0 : (LightRadixKeys.word p0 U0 J : ℤ)≤lim.word)
    (hw1 : (LightRadixKeys.word p1 U1 J : ℤ)≤lim.word)
    (hw2 : (LightRadixKeys.word p2 U2 J : ℤ)≤lim.word)
    (hM : 0<M) (hjoinWord : (LightSourceResidues.word M M U 0 : ℤ)≤lim.word)
    (hlookupWord : ((bank+2^(W+1)+16 : ℕ) : ℤ)≤lim.word)
    (hgroupWord : ((groups*bank+1 : ℕ) : ℤ)≤lim.word)
    (hgroupSpace : groups*bank+1≤lim.space)
    (hfactor : (factor : ℤ)≤lim.word)
    (hweighted : (factor : ℤ)*(count xs p0 J M NL input*weightU : ℕ)≤lim.word)
    (hhistWord : ((count xs p0 J M NL input+1 : ℕ) : ℤ)*weightU≤lim.word)
    (hinput : ∀ i<NL, μ (src+i)=input i) (hinputBound : ∀ i<NL, |input i|≤(U : ℤ))
    (hweightRead : ∀ i<NL, μ (weightBase+i)=weight i)
    (hweightBound : ∀ i<NL, |weight i|≤(weightU : ℤ))
    (hglobal : U0*(p0+1)^J≤U)
    (hcodes : ∀ i<bank, μ (a+i)=(codes i : ℤ))
    (hcodeBound : ∀ i<bank, codes i<2^W)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i<k → k<bank → codes i<codes k)
    (hwordCode : ∀ j<size xs J, dictionary ys p1 J j=(codes (key j) : ℤ))
    (hkey : ∀ j<size xs J, key j<bank)
    (hgroupCode : ∀ j<size xs J, dictionary zs p2 J j=(group j : ℤ))
    (hgroup : ∀ j<size xs J, group j<groups)
    (hL : L≤W) (hn : bank<2^L) (hd : d+NL+L+J+8≤lim.depth) :
    Meets lim (program xs ys zs) 34 d
      [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2,src,NL,M,free,
        a,bank,powers,L,keyBase,valueBase,weightBase,factor,groups] μ
      (time xs ys zs p0 J M NL U L bank groups input)
      (fun r ν => r=(valueBase : ℤ) ∧ Kept μ ν base0 ∧
        ∃ ps : List (ℕ × ℕ), ps.length=count xs p0 J M NL input ∧ ps.Nodup ∧
          (∀ i j, (i,j)∈ps ↔ i<NL ∧ j<size xs J ∧ (M : ℤ)∣input i-dictionary xs p0 J j) ∧
          ∀ r<groups*bank, ν (valueBase+r)=(factor : ℤ)*
            LightTernaryWeightedHistogram.total
              (fun i => group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2)
              (fun i => weight (ps.getD i (0,0)).1) r (count xs p0 J M NL input)) := by sorry
