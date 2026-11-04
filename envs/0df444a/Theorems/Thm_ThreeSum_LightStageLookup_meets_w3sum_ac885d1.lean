-- Prove2me | Theorems.Thm_ThreeSum_LightStageLookup_meets_w3sum_ac885d1
-- name    : ThreeSum.LightStageLookup.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:46:14.869332+00:00
-- url     : https://prove2.me/theorems/8dcb283e-201a-4de9-9693-87daa2240795
-- title:
--   Light Stage Lookup: meets
-- statement:
--   The Light Stage Lookup construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStageLookup.lean#L32-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStageLookup.lean#L32-L73

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5

set_option autoImplicit false
open ThreeSum ThreeSum.LightStageLookup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightStageLookup.meets_w3sum_ac885d1 {pMain pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pSize pAddress))
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    {μ : ℕ → ℤ} {L cut base j work d : ℕ} (S : Finset (Fin L)) (value : ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hS : S.card ≤ cut) (hj : j ≤ L)
    (hread : μ (readAddr cut base j S) = value) (hd : d+L+5 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,S.card,subsetMask S,j,base,work] μ (time L)
      (fun r μ' => r = value ∧ Kept μ μ' work) := by sorry
