-- Prove2me | Theorems.Thm_ThreeSum_LightSourceRetainedStages_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceRetainedStages.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:17:21.569124+00:00
-- url     : https://prove2.me/theorems/0054e0be-c275-43e1-892f-4765891cccbb
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRetainedStages.lean#L60-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRetainedStages.lean#L60-L122

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRetainedStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceRetainedStages.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {raw flags table base m work L cut maskBase E B : ℕ}
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+8 ≤ lim.depth)
    (hm : 0 < m) (hcut : cut ≤ L)
    (hraw : raw+downsetCap L cut ≤ base) (hflags : flags+downsetCap L cut ≤ base)
    (htable : table+m ≤ base) (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hspace : space work L E ≤ lim.space)
    (hword : (word L m E B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < downsetCap L cut,
      μ (raw+i) = endpoint (SourceTableLayout.setAt L cut i))
    (hrawBound : ∀ S, S.card ≤ cut → |endpoint S| ≤ (E : ℤ))
    (hflagRead : ∀ i < downsetCap L cut,
      μ (flags+i) = (flag (SourceTableLayout.setAt L cut i) : ℤ))
    (hflagBound : ∀ S, S.card ≤ cut → flag S ≤ 1)
    (hhistRead : ∀ r < m, μ (table+r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    Meets lim P pMain d [raw,flags,table,base,m,work,L,cut,maskBase,downsetCap L cut]
      μ (time L cut E) (fun _ ν =>
        LightZetaStages.StoredThrough ν base cut (source m endpoint flag hist) L ∧
        Kept μ ν base) := by sorry
