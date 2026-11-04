-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_finiteAllProducts
-- name    : ThreeSum.BandRawA.mem_finiteAllProducts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:38.070055+00:00
-- url     : https://prove2.me/theorems/0a1080eb-4cfc-4dbd-8800-951f9a695e08
-- title:
--   Band Raw A: mem finite All Products
-- statement:
--   The Band Raw A construction uses the mem finite All Products property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L60-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L60-L64

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteAllProducts nA nB nC g rs ↔
      coordinates t ∈ allProducts nA nB nC g rs := by sorry
