-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_oneBlock_storage_bound
-- name    : TunnellMap.BlockGen.oneBlock_storage_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:58:00.18077+00:00
-- url     : https://prove2.me/theorems/f5be8743-1fc2-4a30-addd-ad4ebe946e5e
-- title:
--   Block Gen: one Block storage bound
-- statement:
--   The storage bound implied by the invariant: the generator never holds more
--   records than a single block contains, and never more than the number of
--   candidate indices of that block.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L219-L224
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L219-L224

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.oneBlock_storage_bound (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} (hst : OneBlock s F st) :
    st.pending.length ≤ (blockIndexList n F (st.nextBlock - 1)).length := by sorry
