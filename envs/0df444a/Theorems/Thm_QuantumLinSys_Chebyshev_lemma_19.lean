-- Prove2me | Theorems.Thm_QuantumLinSys_Chebyshev_lemma_19
-- name    : QuantumLinSys.Chebyshev.lemma_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:03.959552+00:00
-- url     : https://prove2.me/theorems/fb10bf7a-25cf-4037-bf1a-b582167d3688
-- title:
--   Lemma 19, p. 21 — the series (77) truncated at j₀ = √(b log(4b/ε)) is ε-close to (1 − (1 − x²)^b)/x on [−1, 1]
-- statement:
--   Let $b \ge 0$ be an integer and $\varepsilon > 0$, and put $j_0 = \sqrt{b\log(4b/\varepsilon)}$. Then the truncation of the series (77),
--   $$g(x) := 4 \sum_{j=0}^{j_0} (-1)^j \left[ \frac{\sum_{i=j+1}^{b} \binom{2b}{b+i}}{2^{2b}} \right] \mathcal T_{2j+1}(x), \tag{88}$$
--   is $\varepsilon$-close on $[-1,1]$ to the function $f_b(x) = \dfrac{1-(1-x^2)^b}{x}$ of (74):
--   $$|g(x) - f_b(x)| \le \varepsilon \qquad \text{for all } x \in [-1,1].$$
--
--   Thus $f_b$ is $\varepsilon$-approximated by a combination of Chebyshev polynomials of order $O(\sqrt{b\log(b/\varepsilon)})$ rather than $2b-1$, which is what reduces the cost of the quantum walk implementation.
--
--   **Formalization Note** The sum runs over $j = 0, \dots, \lfloor j_0 \rfloor$, so $g$ has degree $2\lfloor j_0\rfloor + 1$; the page's order bound $O(\sqrt{b\log(b/\varepsilon)})$ is this degree and is not stated separately. At $x = 0$, $f_b(0)$ is read as $0$ (the continuous extension; see Lemma 18). If $4b/\varepsilon < 1$, Lean's $\log$ and $\sqrt{\cdot}$ give $j_0 = 0$; the statement is still the page's.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 21, Lemma 19 (eq. (88))

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting

namespace QuantumLinSys.Chebyshev

theorem lemma_19 (b : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |chebSum b (j0Of b ε + 1) x - fTamed b x| ≤ ε := by sorry

end QuantumLinSys.Chebyshev
