-- Prove2me | Theorems.Thm_QuantumLinSys_Chebyshev_lemma_18
-- name    : QuantumLinSys.Chebyshev.lemma_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:59.439347+00:00
-- url     : https://prove2.me/theorems/c48456f7-dffb-46cc-b0b5-dc7627f1e102
-- title:
--   Lemma 18, p. 19 — on [−1, 1], (1 − (1 − x²)^b)/x is exactly the odd Chebyshev series (77) of order 2b − 1
-- statement:
--   Let $b \ge 0$ be an integer. Over the domain $[-1,1]$ the function $f_b$ of (74) is exactly a linear combination of the odd Chebyshev polynomials of the first kind of order at most $2b-1$:
--   $$\frac{1-(1-x^2)^b}{x} = 4 \sum_{j=0}^{b-1} (-1)^j \left[ \frac{\sum_{i=j+1}^{b} \binom{2b}{b+i}}{2^{2b}} \right] \mathcal T_{2j+1}(x) \qquad \text{for all } x \in [-1,1].$$
--
--   The identity turns the tamed inverse of Lemma 17 into a Chebyshev series whose coefficients are binomial tail probabilities; that series can be implemented by a quantum walk and truncated (Lemma 19).
--
--   **Formalization Note** At $x = 0$ the left side is understood as its continuous extension (the numerator is a polynomial without constant term). Lean evaluates $f_b(0)$ as $0/0 = 0$, which is that extension's value, since every odd Chebyshev polynomial vanishes at $0$; the identity is therefore stated on all of $[-1,1]$. For $b = 0$ both sides are $0$.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 19, Lemma 18 (eq. (77))

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting

namespace QuantumLinSys.Chebyshev

theorem lemma_18 (b : ℕ) : ∀ x ∈ Set.Icc (-1 : ℝ) 1, fTamed b x = chebSum b b x := by sorry

end QuantumLinSys.Chebyshev
