-- Prove2me | Theorems.Thm_QuantumLinSys_Chebyshev_eq_89
-- name    : QuantumLinSys.Chebyshev.eq_89
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:08.085602+00:00
-- url     : https://prove2.me/theorems/ece736ff-260c-428d-88d2-b71da5ddbbf1
-- title:
--   Eq. (89), p. 21 (proof of Lemma 19) — Chernoff bound: 2^{−2b} Σ_{i=j+1}^{b} C(2b, b+i) ≤ e^{−j²/b}
-- statement:
--   For all integers $b, j \ge 0$, the probability of seeing more than $b+j$ heads on flipping $2b$ fair coins is at most $e^{-j^2/b}$:
--   $$\frac{1}{2^{2b}} \sum_{i=j+1}^{b} \binom{2b}{b+i} \le e^{-j^2/b}.$$
--
--   This is the bound on the coefficients of the Chebyshev series (77) that makes its tail beyond $j_0$ negligible in Lemma 19.
--
--   **Formalization Note** No restriction on $b$ or $j$ is imposed, matching the unrestricted display. At $b = 0$ the left side is the empty sum $0$ and Lean reads $-j^2/0$ as $0$, so the right side is $1$; for $j \ge b$ the left side is the empty sum $0$. Both corners are true and carry no content.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 21, proof of Lemma 19, eq. (89)

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting

namespace QuantumLinSys.Chebyshev

theorem eq_89 (b j : ℕ) : coeff b j ≤ Real.exp (-((j : ℝ) ^ 2) / b) := by sorry

end QuantumLinSys.Chebyshev
