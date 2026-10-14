-- Prove2me | Theorems.Thm_RamanujanPetersson_tau_q_expansion
-- name    : RamanujanPetersson.tau_q_expansion
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:12:44.673379+00:00
-- url     : https://prove2.me/theorems/3e02cdc9-a574-4e27-91b4-657972735f82
-- title:
--   First coefficients of $\Delta$: $q-24q^2+252q^3-1472q^4+4830q^5-\cdots$
-- statement:
--   Let $\tau(n)$ be Ramanujan's tau function, the coefficients of $\Delta(z)=\sum_n\tau(n)q^n$. Then the expansion has no constant term and begins
--
--   $$\Delta(z)=q-24q^2+252q^3-1472q^4+4830q^5-\cdots,$$
--
--   that is,
--
--   1. $\tau(0)=0$, $\tau(1)=1$;
--   2. $\tau(2)=-24$, $\tau(3)=252$;
--   3. $\tau(4)=-1472$, $\tau(5)=4830$.
--
--   These values pin down the normalisation of $\tau$ and serve as a sanity check of the definition.
--
--   **Formalization Note** $\tau$ is `RamanujanPetersson.tau`, the $n$-th coefficient of Mathlib's $q$-expansion (period $1$) of `ModularForm.discriminant`, valued in $\mathbb C$.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan conjecture", displayed expansion $\Delta(z)=\sum_{n=1}^\infty\tau(n)q^n=q-24q^2+252q^3-1472q^4+4830q^5-\cdots$

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem tau_q_expansion :
    tau 0 = 0 ∧ tau 1 = 1 ∧ tau 2 = -24 ∧ tau 3 = 252 ∧ tau 4 = -1472 ∧ tau 5 = 4830 := by sorry

end RamanujanPetersson
