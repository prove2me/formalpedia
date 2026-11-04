-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_word_mono
-- name    : ThreeSum.EncodedColorPrimeCosts.word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:28:48.622413+00:00
-- url     : https://prove2.me/theorems/f1869869-9255-4c8c-b75b-18cf04fae8a8
-- title:
--   Encoded Color Prime Costs: word mono
-- statement:
--   The Encoded Color Prime Costs construction uses the word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L32-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L32-L40

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_LightRadixKeys_word_mono
import Theorems.Thm_ThreeSum_ModuloRuntime_word_mono
import Theorems.Thm_ThreeSum_SourceBandBankLayout_word_mono

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds

theorem ThreeSum.EncodedColorPrimeCosts.word_mono {maxMod nA nB nC nA' nB' nC' g M y U : ℕ}
    (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    LightEncodedColorPrime.word maxMod nA nB nC g M y U ≤
      LightEncodedColorPrime.word maxMod nA' nB' nC' g M y U := by sorry
