-- Prove2me | Theorems.Thm_RamanujanPetersson_petersson_weight_one
-- name    : RamanujanPetersson.petersson_weight_one
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:21:21.625986+00:00
-- url     : https://prove2.me/theorems/a7067957-40d5-43e8-9ad3-441651ffbb35
-- title:
--   Ramanujan–Petersson for cusp forms of weight $1$ (Deligne–Serre 1974)
-- statement:
--   Let $\Gamma\subseteq SL(2,\mathbb Z)$ be a congruence subgroup and let $f$ be a holomorphic cusp form of weight $1$ for $\Gamma$. Let $h>0$ be the width of the cusp $\infty$ for $\Gamma$ and write $f(z)=\sum_{n\ge0}a_n e^{2\pi i n z/h}$. Then for every $\varepsilon>0$,
--
--   $$a_n=O_\varepsilon\!\left(n^{\varepsilon}\right),$$
--
--   which is the bound $n^{(k-1)/2+\varepsilon}$ for $k=1$.
--
--   This weight-one case is due to Deligne and Serre.
--
--   **Formalization Note** Same conventions as the weight $k\ge2$ milestone: Mathlib `CuspForm` for the image of $\Gamma$ in $GL(2,\mathbb R)$, coefficients from `qExpansion` with period `strictWidthInfty`.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan–Petersson conjecture for modular forms": "This is also true for the case $k=1$, where it is a result of Deligne & Serre (1974)"

import Mathlib

open UpperHalfPlane Filter Asymptotics MatrixGroups

namespace RamanujanPetersson

theorem petersson_weight_one (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 1) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (qExpansion (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty f).coeff n)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ ε := by sorry

end RamanujanPetersson
