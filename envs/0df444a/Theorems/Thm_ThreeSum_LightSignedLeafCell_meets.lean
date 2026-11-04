-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
-- name    : ThreeSum.LightSignedLeafCell.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:13:52.299696+00:00
-- url     : https://prove2.me/theorems/188e3939-6df1-454b-9213-7f4af3196845
-- title:
--   Light Signed Leaf Cell: meets
-- statement:
--   The Light Signed Leaf Cell construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafCell.lean#L34-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafCell.lean#L34-L80

import Definitions.Def_Submission_ThreeSum_LightSignedLeafGeneral
import Definitions.Def_Submission_ThreeSum_LightSignedLeafCell
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafCell
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeafCell.meets {pMain pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (body pLeaf pAddress)) (C : Procs P pLeaf pAddress)
    {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR dst work B D d : ℕ}
    (preL preR S : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ work)
    (hdst : dst+downsetCap W boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hS : S.card ≤ boxCut)
    (hcardL : (preL ∪ S).card ≤ sourceCut) (hcardR : (preR ∪ S).card ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+7 ≤ lim.depth) :
    Meets lim P pMain d
      [W,sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        S.card,subsetMask S,baseL,baseR,dst,work] μ (time W)
      (fun _ μ' => μ' (dst+subsetRank S) = SignedLeaf.value f g stage preL preR S ∧
        KeptExcept μ μ' work (dst+subsetRank S)) := by sorry
