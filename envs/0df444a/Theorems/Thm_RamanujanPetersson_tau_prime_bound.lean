-- Prove2me | Theorems.Thm_RamanujanPetersson_tau_prime_bound
-- name    : RamanujanPetersson.tau_prime_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:14:41.687559+00:00
-- url     : https://prove2.me/theorems/127be076-0942-4db7-b8ef-639832726fc0
-- title:
--   Ramanujan's bound $|\tau(p)|\le 2p^{11/2}$ (Deligne 1974)
-- statement:
--   For every prime $p$,
--
--   $$|\tau(p)|\le 2\,p^{11/2}.$$
--
--   This is the third of Ramanujan's 1916 conjectures. It is equivalent to the statement that the polynomial $1-\tau(p)u+p^{11}u^2$ has non-real or double roots, and it follows from Deligne's proof (1974) of the Riemann hypothesis for varieties over finite fields.
--
--   **Formalization Note** $\tau$ is `RamanujanPetersson.tau`, the $n$-th coefficient of Mathlib's $q$-expansion (period $1$) of `ModularForm.discriminant`, valued in $\mathbb C$.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan conjecture", Ramanujan's conjecture 3 ("$|\tau(p)|\le 2p^{11/2}$ for all primes $p$"); proved via Deligne (1974)

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem tau_prime_bound :
    ∀ p : ℕ, p.Prime → ‖tau p‖ ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2) := by sorry

end RamanujanPetersson
