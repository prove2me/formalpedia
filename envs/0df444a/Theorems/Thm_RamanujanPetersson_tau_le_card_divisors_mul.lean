-- Prove2me | Theorems.Thm_RamanujanPetersson_tau_le_card_divisors_mul
-- name    : RamanujanPetersson.tau_le_card_divisors_mul
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:15:40.76743+00:00
-- url     : https://prove2.me/theorems/3db8e1a5-b36b-4cd7-9e86-3eef7233146a
-- title:
--   Divisor bound $|\tau(n)|\le d(n)\,n^{11/2}$
-- statement:
--   For every integer $n\ge1$,
--
--   $$|\tau(n)|\le d(n)\,n^{11/2},$$
--
--   where $d(n)$ is the number of positive divisors of $n$.
--
--   As noted by Ramanujan, this follows from his three conjectures. It extends the prime bound to all $n$.
--
--   **Formalization Note** $\tau$ is `RamanujanPetersson.tau`, the $n$-th coefficient of Mathlib's $q$-expansion (period $1$) of `ModularForm.discriminant`, valued in $\mathbb C$. $d(n)$ is the cardinality of `n.divisors`.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan conjecture", paragraph after conjecture 3 ("these conjectures imply that $|\tau(n)|\le d(n)n^{11/2}$ for all $n\ge1$")

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem tau_le_card_divisors_mul :
    ∀ n : ℕ, 1 ≤ n → ‖tau n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ ((11 : ℝ) / 2) := by sorry

end RamanujanPetersson
