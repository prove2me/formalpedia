-- Prove2me | Theorems.Thm_RamanujanPetersson_tau_partial_sum_isBigO
-- name    : RamanujanPetersson.tau_partial_sum_isBigO
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:16:37.25499+00:00
-- url     : https://prove2.me/theorems/7b9764a4-9c8c-41be-90d9-d2dd5cf52403
-- title:
--   Partial sums $\sum_{k\le n}\tau(k)=O(n^{13/2+\varepsilon})$
-- statement:
--   For every $\varepsilon>0$,
--
--   $$\sum_{k=1}^{n}\tau(k)=O\!\left(n^{13/2+\varepsilon}\right)\qquad(n\to\infty).$$
--
--   The source presents this as the general estimate behind the absolute convergence of the Ramanujan $L$-series.
--
--   **Formalization Note** $\tau$ is `RamanujanPetersson.tau`, the $n$-th coefficient of Mathlib's $q$-expansion (period $1$) of `ModularForm.discriminant`, valued in $\mathbb C$.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan L-function", display "From general estimation for tau function $\sum_{k=1}^n\tau(k)=O(n^{13/2+\epsilon})$"

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem tau_partial_sum_isBigO (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, tau k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ ((13 : ℝ) / 2 + ε) := by sorry

end RamanujanPetersson
