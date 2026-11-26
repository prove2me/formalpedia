-- Prove2me | Theorems.Thm_TunnellMap_paperTunnellMapTotal_residual_target
-- name    : TunnellMap.paperTunnellMapTotal_residual_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:02:27.658553+00:00
-- url     : https://prove2.me/theorems/3cbd8568-9a94-5cfb-b2d9-1e055d932e26
-- title:
--   Tunnell Map: paper Tunnell Map Total residual target
-- statement:
--   **The residual branch lands in the residual targets.**  A source whose
--   third coordinate is odd and which satisfies none of the three congruences is
--   mapped to a target that no quarter-turn branch produces; the value there is
--   the one computed by the generator and the deferred-acceptance loop.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L114-L136
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BranchSpec.lean#L114-L136

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.paperTunnellMapTotal_residual_target (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0) (hd : ¬ SourceUsedTriple p.1) :
    ¬ DirectTargetUsed (paperTunnellMapTotal hn hnpos hsq hbal p) := by sorry
