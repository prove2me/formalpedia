-- Prove2me | Theorems.Thm_TunnellMap_oddEquivOfBalance_apply_direct
-- name    : TunnellMap.oddEquivOfBalance_apply_direct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:14:49.493539+00:00
-- url     : https://prove2.me/theorems/150b5817-ced8-4d0d-b421-18dbd5b40f4e
-- title:
--   Tunnell Map: odd Equiv Of Balance apply direct
-- statement:
--   The Tunnell Map construction uses the odd Equiv Of Balance apply direct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L36-L46
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L36-L46

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
import Definitions.Def_TunnellMap_ComputableFullMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.oddEquivOfBalance_apply_direct (hn : Odd n) (hnpos : 0 < n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (q : BOddRep n) (hd : DirectSourceUsed q) :
    oddEquivOfBalance hn hnpos hbal q = (directSubsetEquiv hn ⟨q, hd⟩).1 := by sorry
