-- Prove2me | Theorems.Thm_StreamingWeightedSetCover1523_LowerBound_lemma_3_1
-- name    : StreamingWeightedSetCover1523.LowerBound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:20.157629+00:00
-- url     : https://prove2.me/theorems/9fbe1afa-5862-4563-bd6c-ead3dc98f79f
-- title:
--   Lemma 3.1 — transcripts and protocol nodes are rectangles
-- statement:
--   Let $\pi$ be a deterministic two-party protocol tree with Alice's inputs in $X$ and Bob's in $Y$ (random bits fixed): every internal node is owned by one player and labelled with a bit-valued function of that player's input, every leaf with an output bit.
--
--   1. For every transcript $\tau$ (bit sequence), the set of input pairs whose transcript is $\tau$ is a rectangle $R_\tau\times T_\tau$.
--   2. More generally, for every node $\tau$ of the tree (named by the bits sent so far), the set $S_\tau$ of input pairs whose run passes through $\tau$ is a rectangle $R_\tau\times T_\tau$.
--
--   No input distribution is involved, so the lemma applies equally to correlated inputs.
--
--   Differences from the source:
--   - generalization: input sets X = (F₂^v)^r and Y = (F₂^v)^s → arbitrary types X and Y; reason: the statement does not use the input structure; it specializes to the blocks
--   - encoding: nodes of the protocol tree, identified with sequences of bits sent so far → every bit sequence w; a sequence that is not a node gives the empty set, the rectangle ∅ × ∅; reason: same identification as the source; non-nodes add only trivial cases
--   - encoding: binary protocol tree with owners, message functions and output bits → the published DetCCHard.Protocol (bit true selects the child p₁); reason: same object
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), Lemma 3.1, printed p. 12 (PDF p. 13); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound

/-- Lemma 3.1 (PDF p. 13): for a deterministic protocol tree (fixed random bits), the set of input
pairs with a given transcript is a rectangle, and more generally the set of input pairs whose run
passes through any node `w` of the tree is a rectangle. -/
theorem lemma_3_1 {X Y : Type} (π : DetCCHard.Protocol X Y) :
    (∀ τ : List Bool, ∃ (R : Set X) (T : Set Y),
      {xy : X × Y | protocolTranscript π xy.1 xy.2 = τ} = R ×ˢ T) ∧
    (∀ w : List Bool, ∃ (R : Set X) (T : Set Y),
      {xy : X × Y | protocolReaches π w xy.1 xy.2} = R ×ˢ T) := by sorry

end StreamingWeightedSetCover1523.LowerBound
