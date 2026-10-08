-- Prove2me | Theorems.Thm_QuantumLinSys_Chebyshev_lemma_17
-- name    : QuantumLinSys.Chebyshev.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:59.997751+00:00
-- url     : https://prove2.me/theorems/f0c9a13a-4aad-41a9-93c4-2342d75e58dd
-- title:
--   Lemma 17, p. 19 — (1 − (1 − x²)^b)/x is ε-close to 1/x on D_{κd} for every integer b ≥ (κd)² log(κd/ε)
-- statement:
--   Let $\kappa \ge 1$, let $d \ge 1$ be an integer (the sparsity of the matrix), let $\varepsilon > 0$, and let $b \ge 0$ be an integer with
--   $$b \ge (\kappa d)^2 \log(\kappa d/\varepsilon).$$
--   Then the function $f_b(x) = \dfrac{1-(1-x^2)^b}{x}$ of (74) is $\varepsilon$-close to $1/x$ on $D_{\kappa d} = [-1,-1/(\kappa d)] \cup [1/(\kappa d), 1]$:
--   $$\left| \frac{1-(1-x^2)^b}{x} - \frac1x \right| \le \varepsilon \qquad \text{for all } x \in D_{\kappa d}.$$
--
--   Multiplying $1/x$ by $1-(1-x^2)^b$ removes the singularity at the origin while changing the function by at most $\varepsilon$ on the domain where the eigenvalues of the rescaled matrix lie; the result is a polynomial, which Lemma 18 expands in Chebyshev polynomials.
--
--   **Formalization Note** $\kappa \ge 1$ (a condition number) and $d \ge 1$ (a sparsity) are made explicit; they make $D_{\kappa d}$ nonempty and keep $0$ out of it. The page's "integer $b$" is a natural number: $f_b$ is "a polynomial of degree $2b-1$" (p. 19), and a negative exponent would make $(1-x^2)^b$ singular at $x = \pm 1$.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 19, Lemma 17 (eq. (74))

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting

namespace QuantumLinSys.Chebyshev

theorem lemma_17 (κ ε : ℝ) (d b : ℕ) (hκ : 1 ≤ κ) (hd : 1 ≤ d) (hε : 0 < ε)
    (hb : (κ * d) ^ 2 * Real.log (κ * d / ε) ≤ b) :
    ∀ x ∈ Dκ (κ * d), |fTamed b x - 1 / x| ≤ ε := by sorry

end QuantumLinSys.Chebyshev
