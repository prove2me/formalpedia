-- Prove2me | Theorems.Thm_PrivateRoutingSignaling_PTAS_flow_rounding
-- name    : PrivateRoutingSignaling.PTAS.flow_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:00.963224+00:00
-- url     : https://prove2.me/theorems/7f96f355-83c5-4721-943c-2dfd0ddc9da7
-- title:
--   Lemma 3.1 — mean-preserving uniform-flow rounding
-- statement:
--   Let $s\in\Delta_P$ be any real unit-demand flow in a finite directed network in which every simple source-sink path has at most $d$ arcs. For every positive integer $k$, there is a distribution $F$ on the entire grid of $k$-uniform flows such that
--
--   $$\mathbb E_{s'\sim F}[s'_p]=s_p\quad(p\in P),$$
--   $$|x_i(s')-x_i(s)|\le\frac{2d}{k}\quad\text{for every arc }i\text{ and every supported }s'.$$
--
--   The input traffic and probability weights are arbitrary reals. Every supported output is a feasible flow, and the absolute congestion guarantee holds simultaneously for all arcs. This is the rounding interface needed to compare the finite LP with the exactly obedient continuous optimum.
--
--   Differences from the source:
--   - encoding: ε>0 with 1/ε an integer → a positive natural number k=1/ε and discrepancy 2d/k; reason: positive integral reciprocals and positive natural denominators give exactly the same grids and error bounds
--   - encoding: a distribution over all uniform flows → real probability weights on integer path-count vectors of total k; reason: division by k bijects this finite carrier with the full grid; positive weights specify support
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #439 (October 2026), Lemma 3.1, p. 10 (PDF p. 10); proof p. 13 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Network

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS

/-- Lemma 3.1, p.10. k is the positive integer 1/ε; probabilities and input flows are real. -/
theorem flow_rounding (N : RoutingNetwork) (hN : NetworkValid N)
    (s : Flow N) (k : ℕ) (hk : 0 < k) :
    ∃ w : Grid N k → ℝ, FiniteLaw w ∧
      (∀ p, ∑ a, w a * gridVector N k a p = s.val p) ∧
      ∀ a, 0 < w a → IsFlow N (gridVector N k a) ∧
        ∀ i : Fin N.arcs,
          |arcLoad N (gridVector N k a) i - arcLoad N s.val i| ≤ 2 * (N.d : ℝ) / k := by sorry

end PrivateRoutingSignaling.PTAS
