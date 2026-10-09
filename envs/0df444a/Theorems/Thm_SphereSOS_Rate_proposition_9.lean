-- Prove2me | Theorems.Thm_SphereSOS_Rate_proposition_9
-- name    : SphereSOS.Rate.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:38.72697+00:00
-- url     : https://prove2.me/theorems/5a3afe03-33ba-4051-b963-c8305b3b9b83
-- title:
--   Proposition 9, p. 9 — if $\tilde\rho<1$ then $\rho\le\tilde\rho/(1-\tilde\rho)$
-- statement:
--   Let $d\ge2$, $n\ge0$, $\ell\ge0$, and write $\rho=\rho_{2n}(d,\ell)$ and $\tilde\rho=\tilde\rho_{2n}(d,\ell)$. If $\tilde\rho<1$, then
--   $$\rho\le\frac{\tilde\rho}{1-\tilde\rho}.$$
--
--   This transfers the bound on the linear proxy $\tilde\rho$, which is an eigenvalue problem, to the quantity $\rho$ that appears in the certificate of Theorem 6.
--
--   **Formalization Note** $\rho$ takes values in $[0,\infty]$ and the right side is embedded there. The hypothesis $\tilde\rho<1$ makes the feasible set of $\rho$ nonempty with all $\lambda_{2k}>0$, so no junk value is involved.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 9, Proposition 9, with ρ from (10)/(13) and ρ̃ from (16)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Rho

namespace SphereSOS.Rate

theorem proposition_9 (d n ℓ : ℕ) (hd : 2 ≤ d) (hlt : rhoTilde d n ℓ < 1) :
    rho d n ℓ ≤ ENNReal.ofReal (rhoTilde d n ℓ / (1 - rhoTilde d n ℓ)) := by sorry

end SphereSOS.Rate
