-- Prove2me | Theorems.Thm_ThreeSum_SubsetTransport_mobius_partial_product_map
-- name    : ThreeSum.SubsetTransport.mobius_partial_product_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:51.210673+00:00
-- url     : https://prove2.me/theorems/2b20c435-1ba9-463b-a729-2ff207bec7a1
-- title:
--   Subset Transport: mobius partial product map
-- statement:
--   The Subset Transport construction uses the mobius partial product map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L51-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L51-L61

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem ThreeSum.SubsetTransport.mobius_partial_product_map (e : α ≃ β) (f g : Finset α → ℤ)
    (processed preL preR Q : Finset α) :
    Subset.mobius (fun S =>
      Subset.partialZeta (processed.map e.toEmbedding) (reindex e f) (preL.map e.toEmbedding ∪ S) *
      Subset.partialZeta (processed.map e.toEmbedding) (reindex e g) (preR.map e.toEmbedding ∪ S))
      (Q.map e.toEmbedding) =
      Subset.mobius (fun S => Subset.partialZeta processed f (preL ∪ S) *
        Subset.partialZeta processed g (preR ∪ S)) Q := by sorry
