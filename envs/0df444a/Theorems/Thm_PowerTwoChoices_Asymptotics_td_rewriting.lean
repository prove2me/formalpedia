-- Prove2me | Theorems.Thm_PowerTwoChoices_Asymptotics_td_rewriting
-- name    : PowerTwoChoices.Asymptotics.td_rewriting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:57.307977+00:00
-- url     : https://prove2.me/theorems/36f09c39-7f4b-487b-907a-405ecaec8afe
-- title:
--   Proof of Theorem 4, display: $T_d(\lambda)=\sum_{i\ge1}(\lambda')^{d^i}/\lambda^{d/(d-1)}$ with $\lambda'=\lambda^{1/(d-1)}$
-- statement:
--   Let $d\ge2$ be an integer and $0<\lambda<1$, and put $\lambda'=\lambda^{1/(d-1)}$ (the positive real root). Then the series $\sum_{i\ge1}(\lambda')^{d^i}$ converges and
--   $$T_d(\lambda)=\sum_{i=1}^{\infty}\lambda^{\frac{d^i-d}{d-1}}=\frac{\sum_{i=1}^{\infty}(\lambda')^{d^i}}{\lambda^{d/(d-1)}} .$$
--
--   This rewriting expresses $T_d(\lambda)$ through the lacunary series $\sum_i x^{d^i}$ evaluated at $x=\lambda'$, which is how the paper reduces Theorem 4 to Lemma 3.
--
--   **Formalization Note.** $\lambda'$ and $\lambda^{d/(d-1)}$ are real powers (`Real.rpow`); $(\lambda')^{d^i}$ is a natural-number power. Both sums over $i\ge1$ are written over $i\in\mathbb N$ with the $i=0$ term set to $0$. The hypothesis $\lambda>0$ is needed because the identity divides by $\lambda^{d/(d-1)}$.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1099, proof of Theorem 4, display

import Mathlib
import Definitions.Def_PowerTwoChoices_Asymptotics_ExpectedTime

open Filter Topology

namespace PowerTwoChoices.Asymptotics

/-- The rewriting of `T_d` in the proof of Theorem 4 (Mitzenmacher 2001, p. 1099): for `d ≥ 2`
and `0 < λ < 1`, with `λ' = λ^{1/(d-1)}` (real power), the series `∑_{i ≥ 1} (λ')^{d^i}`
converges and
`T_d(λ) = (∑_{i ≥ 1} (λ')^{d^i}) / λ^{d/(d-1)}`. -/
theorem td_rewriting (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    Summable (fun i : ℕ => if 1 ≤ i then (lam ^ (1 / ((d : ℝ) - 1))) ^ (d ^ i) else 0) ∧
      Td d lam =
        (∑' i : ℕ, if 1 ≤ i then (lam ^ (1 / ((d : ℝ) - 1))) ^ (d ^ i) else 0) /
          lam ^ ((d : ℝ) / ((d : ℝ) - 1)) := by sorry

end PowerTwoChoices.Asymptotics
