-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_rectangular_net_reduction
-- name    : PlanarMetricElections.Peer.rectangular_net_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:54.150211+00:00
-- url     : https://prove2.me/theorems/0c365569-7a5e-4aba-9136-3dda91ffaff7
-- title:
--   Lemma 5.6 — rectangular-net reduction
-- statement:
--   For every positive integer $k$, let $\mathrm{PF}_{d_1}(k)$ be the worst-case strong-peer factor for Manhattan distance, and let $\varsigma_k^{\mathcal R}$ be the worst-case strong rectangular net factor. Then
--
--   $$\mathrm{PF}_{d_1}(k)\le\varsigma_k^{\mathcal R}.$$
--
--   The defender chooses a nonempty subset of at most $k$ voters, while the challenger chooses any real planar point. This comparison transfers rectangular-net thresholds to strong peer selection.
--
--   Differences from the source:
--   - encoding: positive integers k → k of type ℕ+; reason: the type contains exactly the positive natural budgets in the source
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Lemma 5.6, p. 11 (PDF p. 12)

import Definitions.Def_PlanarMetricElections_Peer_Capture
import Definitions.Def_PlanarMetricElections_Peer_RectangularNet

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer

theorem rectangular_net_reduction (k : ℕ+) :
    peerFactor dOne k ≤ rectangularFactor k := by sorry

end PlanarMetricElections.Peer
