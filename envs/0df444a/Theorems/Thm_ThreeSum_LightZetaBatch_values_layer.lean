-- Prove2me | Theorems.Thm_ThreeSum_LightZetaBatch_values_layer
-- name    : ThreeSum.LightZetaBatch.values_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:46:04.576786+00:00
-- url     : https://prove2.me/theorems/4f8b24cf-f264-4bd3-abd3-e742ea3db950
-- title:
--   Light Zeta Batch: values layer
-- statement:
--   The Light Zeta Batch construction uses the values layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaBatch.lean#L128-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaBatch.lean#L128-L133

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightZetaBatch
set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaBatch.values_layer {L cardinal : ℕ} (μ : ℕ → ℤ) (dst : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) :
    values μ dst (enumerateLayer L cardinal) a f S =
      if S.card = cardinal then Subset.zetaStep a f S else μ (dst+subsetRank S) := by sorry
