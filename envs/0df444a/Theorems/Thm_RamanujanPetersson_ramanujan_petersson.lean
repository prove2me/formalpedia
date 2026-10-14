-- Prove2me | Theorems.Thm_RamanujanPetersson_ramanujan_petersson
-- name    : RamanujanPetersson.ramanujan_petersson
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:21:43.123993+00:00
-- url     : https://prove2.me/theorems/3c5fc8a7-91a1-4082-8d56-e8060c83c825
-- title:
--   Ramanujan–Petersson conjecture for holomorphic cusp forms
-- statement:
--   Let $\Gamma\subseteq SL(2,\mathbb Z)$ be a congruence subgroup (it contains $\Gamma(N)$ for some $N\ge1$), let $k\ge1$ be an integer, and let $f$ be a holomorphic cusp form of weight $k$ for $\Gamma$. Let $h>0$ be the width of the cusp $\infty$ for $\Gamma$ and write $f(z)=\sum_{n\ge0}a_n e^{2\pi i n z/h}$. Then for every $\varepsilon>0$,
--
--   $$a_n=O_\varepsilon\!\left(n^{(k-1)/2+\varepsilon}\right).$$
--
--   This is the Ramanujan–Petersson conjecture for holomorphic cusp forms, proved by Deligne for $k\ge2$ and by Deligne–Serre for $k=1$. For $\Delta$ ($k=12$, $\Gamma=SL(2,\mathbb Z)$) it gives $\tau(n)=O(n^{11/2+\varepsilon})$.
--
--   **Formalization Note** $\Gamma$ is mapped into $GL(2,\mathbb R)$, $f$ is a Mathlib `CuspForm`, and $a_n$ is the $n$-th coefficient of `qExpansion` with period $h=$ `strictWidthInfty` of $\Gamma$. This period equals $1$ when $z\mapsto z+1$ lies in $\Gamma$, for example for $\Gamma_0(N)$ and $\Gamma_1(N)$, so there $a_n$ are the usual coefficients in $q=e^{2\pi iz}$.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), introduction ("for any cusp form of weight $k$ with Fourier coefficients $a_n$ and every $\epsilon>0$ … $a_n=O_\epsilon(n^{(k-1)/2+\epsilon})$") and section "Ramanujan–Petersson conjecture for modular forms" (holomorphic cusp forms for congruence subgroups; Deligne for $k\ge2$, Deligne & Serre for $k=1$)

import Mathlib

open UpperHalfPlane Filter Asymptotics MatrixGroups

namespace RamanujanPetersson

theorem ramanujan_petersson (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) (k : ℤ) (hk : 1 ≤ k)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (qExpansion (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty f).coeff n)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (((k : ℝ) - 1) / 2 + ε) := by sorry

end RamanujanPetersson
