-- Prove2me | Theorems.Thm_TunnellMap_oddEquivOfBalance_apply_residual
-- name    : TunnellMap.oddEquivOfBalance_apply_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:12:53.93153+00:00
-- url     : https://prove2.me/theorems/ff23a610-d286-5904-87cd-d4d85a5f265a
-- title:
--   Tunnell Map: odd Equiv Of Balance apply residual
-- statement:
--   The Tunnell Map construction uses the odd Equiv Of Balance apply residual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L48-L60
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L48-L60

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
import Definitions.Def_TunnellMap_ComputableFullMap
import Theorems.Thm_TunnellMap_residual_orbit_card_eq

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.oddEquivOfBalance_apply_residual (hn : Odd n) (hnpos : 0 < n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (q : BOddRep n) (hd : ¬ DirectSourceUsed q) :
    oddEquivOfBalance hn hnpos hbal q =
      (residualEquivOfOrbitCard hnpos (residual_orbit_card_eq hn hnpos hbal)
        ⟨q, hd⟩).1 := by sorry
