-- Prove2me | Theorems.Thm_SphereSOS_Rate_theorem_6_second
-- name    : SphereSOS.Rate.theorem_6_second
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:46.471713+00:00
-- url     : https://prove2.me/theorems/a0bd597e-8687-4c08-bb83-d7c01fe25248
-- title:
--   Theorem 6 (second part), p. 7 — for $n\le d$ and $\ell\ge C'_nd$, $\rho_{2n}(d,\ell)\le C_n(d/\ell)^2$
-- statement:
--   For every $n\ge0$ there are constants $C_n,C'_n$, depending only on $n$, such that for all $d\ge2$ with $n\le d$ and all $\ell\ge C'_nd$,
--   $$\rho_{2n}(d,\ell)\le C_n\Big(\frac d\ell\Big)^2.$$
--
--   Combined with the first part of Theorem 6 and $B_{2n}$ from Proposition 5, this gives the quadratic rate of Theorem 2.
--
--   **Formalization Note** The letters follow the page: here $C'_n$ bounds the level and $C_n$ the value. The constants come before $d$ and $\ell$. $\rho_{2n}$ is valued in $[0,\infty]$, so the bound also asserts finiteness. $d\ge2$ is the standing assumption of §2–3. The explicit constants $\ell\ge2nd\Rightarrow\rho_{2n}\le2n^2(d/\ell)^2$ claimed at the end of p. 9 rest on Proposition 7, which is false as printed, and are not asserted.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 7, Theorem 6, second paragraph

import Mathlib
import Definitions.Def_SphereSOS_Rate_Rho

namespace SphereSOS.Rate

theorem theorem_6_second :
    ∀ n : ℕ, ∃ C C' : ℝ, ∀ d ℓ : ℕ,
      2 ≤ d → n ≤ d → C' * (d : ℝ) ≤ (ℓ : ℝ) →
      rho d n ℓ ≤ ENNReal.ofReal (C * ((d : ℝ) / (ℓ : ℝ)) ^ 2) := by sorry

end SphereSOS.Rate
