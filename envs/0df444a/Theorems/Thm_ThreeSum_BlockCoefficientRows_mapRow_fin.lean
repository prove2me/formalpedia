-- Prove2me | Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_fin
-- name    : ThreeSum.BlockCoefficientRows.mapRow_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:35:10.288204+00:00
-- url     : https://prove2.me/theorems/148dfb09-9a12-4d89-8aad-97d92e44db7f
-- title:
--   Block Coefficient Rows: map Row fin
-- statement:
--   The Block Coefficient Rows construction uses the map Row fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L64-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L64-L66

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds

theorem ThreeSum.BlockCoefficientRows.mapRow_fin {h : ℕ} (b : Bool) (s : Occurrence h) (i : Fin (512*h)) :
    mapRow h b s.val i.val = (mapAt h s (i,b)).val := by sorry
