-- Prove2me | Theorems.Thm_QuantumLinSys_Chebyshev_lemma_14
-- name    : QuantumLinSys.Chebyshev.lemma_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:07.593977+00:00
-- url     : https://prove2.me/theorems/2beab768-4307-471a-91ec-a0ea8542a079
-- title:
--   Lemma 14, p. 16 — the Chebyshev series (55) truncated at j₀ = √(b log(4b/ε)), b = κ² log(κ/ε), is 2ε-close to 1/x on D_κ
-- statement:
--   Let $\kappa \ge 1$ and $\varepsilon > 0$. Put $b = \kappa^2 \log(\kappa/\varepsilon)$ and $j_0 = \sqrt{b \log(4b/\varepsilon)}$, and let
--   $$g(x) := 4 \sum_{j=0}^{j_0} (-1)^j \left[ \frac{\sum_{i=j+1}^{b} \binom{2b}{b+i}}{2^{2b}} \right] \mathcal T_{2j+1}(x), \tag{55}$$
--   where $\mathcal T_m$ is the $m$-th Chebyshev polynomial of the first kind. Then $g$ is $2\varepsilon$-close to $1/x$ on $D_\kappa = [-1,-1/\kappa] \cup [1/\kappa,1]$:
--   $$\left| g(x) - \frac1x \right| \le 2\varepsilon \qquad \text{for all } x \in D_\kappa.$$
--
--   This is the decomposition of $1/x$ into odd Chebyshev polynomials of degree $O(\kappa\log(\kappa/\varepsilon))$ on which the Chebyshev-based quantum linear systems algorithm (Theorem 4 of the paper) is built: applied to a Hermitian matrix with spectrum in $D_\kappa$, the same combination of Chebyshev polynomials of the matrix approximates its inverse.
--
--   **Formalization Note** $\kappa \ge 1$ is a condition number (ratio of the largest to the smallest singular value, p. 3); it makes $D_\kappa$ nonempty and keeps $0$ out of it. The page's real $b$ is rounded up, $b = \lceil \kappa^2\log(\kappa/\varepsilon)\rceil$ (it is an exponent, and this keeps the hypothesis of Lemma 17), and the sum runs over $j = 0,\dots,\lfloor j_0\rfloor$. No upper bound on $\varepsilon$ is assumed: if $\varepsilon \ge \kappa$ then $b = 0$, $g \equiv 0$ and $|1/x| \le \kappa \le \varepsilon$ on $D_\kappa$, so the statement is still true there.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 16, Lemma 14 (eq. (55))

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting

namespace QuantumLinSys.Chebyshev

theorem lemma_14 (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) :
    ∀ x ∈ Dκ κ, |chebSum (bOf κ ε) (j0Of (bOf κ ε) ε + 1) x - 1 / x| ≤ 2 * ε := by sorry

end QuantumLinSys.Chebyshev
