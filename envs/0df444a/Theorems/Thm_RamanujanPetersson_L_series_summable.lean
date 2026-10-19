-- Prove2me | Theorems.Thm_RamanujanPetersson_L_series_summable
-- name    : RamanujanPetersson.L_series_summable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T16:17:23.245856+00:00
-- url     : https://prove2.me/theorems/0ebc5789-f790-4652-9f0a-077e6bd419e7
-- title:
--   Absolute convergence of $L(s,\tau)$ for $\operatorname{Re}s>13/2$
-- statement:
--   For every complex $s$ with $\operatorname{Re}s>13/2$, the Ramanujan $L$-series
--
--   $$L(s,\tau)=\sum_{n=1}^{\infty}\frac{\tau(n)}{n^{s}}$$
--
--   converges absolutely.
--
--   This gives the half-plane on which $L(s,\tau)$ is defined by its Dirichlet series. It is also where the Euler product is stated.
--
--   **Formalization Note** $\tau$ is `RamanujanPetersson.tau`, the $n$-th coefficient of Mathlib's $q$-expansion (period $1$) of `ModularForm.discriminant`, valued in $\mathbb C$. Absolute convergence is Mathlib's `LSeriesSummable`.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan L-function", definition $L(s,\tau)=\sum_{n\ge1}\tau(n)/n^s$ and "so this series converges absolutely for $\operatorname{Re}(s)>13/2$"

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem L_series_summable (s : ℂ) (hs : 13 / 2 < s.re) :
    LSeriesSummable tau s := by sorry

end RamanujanPetersson
