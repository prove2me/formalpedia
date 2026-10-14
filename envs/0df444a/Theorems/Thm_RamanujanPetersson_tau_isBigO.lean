-- Prove2me | Theorems.Thm_RamanujanPetersson_tau_isBigO
-- name    : RamanujanPetersson.tau_isBigO
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:16:10.546724+00:00
-- url     : https://prove2.me/theorems/50d6e12e-6b72-405f-b467-b6d73bc4a51c
-- title:
--   $\tau(n)=O(n^{11/2+\varepsilon})$
-- statement:
--   For every $\varepsilon>0$ there is a constant $C_\varepsilon$ such that, for all sufficiently large $n$,
--
--   $$|\tau(n)|\le C_\varepsilon\, n^{11/2+\varepsilon},$$
--
--   that is, $\tau(n)=O(n^{11/2+\varepsilon})$. This is the Ramanujan–Petersson bound for $\Delta$ (weight $12$), and it is a special case of the mission goal.
--
--   **Formalization Note** $\tau$ is `RamanujanPetersson.tau`, the $n$-th coefficient of Mathlib's $q$-expansion (period $1$) of `ModularForm.discriminant`, valued in $\mathbb C$. The bound is Mathlib's big-O along `atTop` on $\mathbb N$.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan conjecture", display "A classic bound on $d(n)$ thus yields $\tau(n)=O(n^{11/2+\epsilon})$"; also section "Ramanujan L-function" ("this estimate was proven unconditionally")

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem tau_isBigO (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => tau n) =O[atTop] fun n : ℕ => (n : ℝ) ^ ((11 : ℝ) / 2 + ε) := by sorry

end RamanujanPetersson
