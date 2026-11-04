-- Prove2me | Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
-- name    : ThreeSum.LightSourceStages.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:06:57.924776+00:00
-- url     : https://prove2.me/theorems/c02843e2-3761-4cae-a302-4789c14912b2
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceStages.lean#L108-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceStages.lean#L108-L170

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceStages.Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {src N raw flags p m hist base codes work L cut maskBase U D E : ℕ} {shift : ℤ}
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+8 ≤ lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hcut : cut ≤ L)
    (hsrc : src+N ≤ hist)
    (hraw : raw+downsetCap L cut ≤ hist) (hflags : flags+downsetCap L cut ≤ hist)
    (hhist : hist+m ≤ base) (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : space work L p U D E ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word N L p m U D E : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hrawRead : ∀ i < downsetCap L cut,
      μ (raw+i) = endpoint (SourceTableLayout.setAt L cut i))
    (hrawBound : ∀ S, S.card ≤ cut → |endpoint S| ≤ (E : ℤ))
    (hflagRead : ∀ i < downsetCap L cut,
      μ (flags+i) = (flag (SourceTableLayout.setAt L cut i) : ℤ))
    (hflagBound : ∀ S, S.card ≤ cut → flag S ≤ 1) :
    Meets lim P pMain d [src,N,raw,flags,p,m,hist,base,codes,work,shift,L,cut,maskBase,downsetCap L cut]
      μ (time N L cut p m U D E) (fun _ ν =>
        LightZetaStages.StoredThrough ν base cut (source μ src N p m shift endpoint flag) L ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N : ℤ)) ∧
        Kept μ ν hist) := by sorry
