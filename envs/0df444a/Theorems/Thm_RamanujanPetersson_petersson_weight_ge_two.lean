-- Prove2me | Theorems.Thm_RamanujanPetersson_petersson_weight_ge_two
-- name    : RamanujanPetersson.petersson_weight_ge_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:21:07.998909+00:00
-- url     : https://prove2.me/theorems/0958926b-9961-4506-bc3d-3f1b7846b2a5
-- title:
--   Ramanujan–Petersson for cusp forms of weight $k\ge2$ (Deligne 1971/1974)
-- statement:
--   Let $\Gamma\subseteq SL(2,\mathbb Z)$ be a congruence subgroup (it contains $\Gamma(N)$ for some $N\ge1$), let $k\ge 2$ be an integer, and let $f$ be a holomorphic cusp form of weight $k$ for $\Gamma$. Let $h>0$ be the width of the cusp $\infty$ for $\Gamma$ and write $f(z)=\sum_{n\ge0}a_n e^{2\pi i n z/h}$. Then for every $\varepsilon>0$,
--
--   $$a_n=O_\varepsilon\!\left(n^{(k-1)/2+\varepsilon}\right).$$
--
--   This is the case of the Ramanujan–Petersson conjecture that Deligne reduced to the Weil conjectures via the Eichler–Shimura isomorphism, and then proved.
--
--   **Formalization Note** $\Gamma$ is mapped into $GL(2,\mathbb R)$, $f$ is a Mathlib `CuspForm`, and $a_n$ is the $n$-th coefficient of `qExpansion` with period $h=$ `strictWidthInfty` of $\Gamma$, which equals $1$ when $z\mapsto z+1$ lies in $\Gamma$.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan–Petersson conjecture for modular forms": statement $a_n=O(n^{(k-1)/2+\epsilon})$ for holomorphic cusp forms for congruence subgroups, and "Deligne (1971) used the Eichler–Shimura isomorphism to reduce this conjecture to the Weil conjectures that he later proved"

import Mathlib

open UpperHalfPlane Filter Asymptotics MatrixGroups

namespace RamanujanPetersson

theorem petersson_weight_ge_two (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) (k : ℤ) (hk : 2 ≤ k)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (qExpansion (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty f).coeff n)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (((k : ℝ) - 1) / 2 + ε) := by sorry

end RamanujanPetersson
