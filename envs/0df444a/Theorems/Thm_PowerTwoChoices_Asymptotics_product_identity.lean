-- Prove2me | Theorems.Thm_PowerTwoChoices_Asymptotics_product_identity
-- name    : PowerTwoChoices.Asymptotics.product_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:07.636987+00:00
-- url     : https://prove2.me/theorems/56d6c799-5b1a-49da-b2ef-eca8b3f4378f
-- title:
--   Proof of Lemma 3, display: $\prod_{i\ge0}(1+\lambda^{d^i}+\dots+\lambda^{(d-1)d^i})=1/(1-\lambda)$
-- statement:
--   Let $d\ge2$ be an integer and $0\le\lambda<1$. Then the infinite product
--   $$\prod_{i=0}^{\infty}\bigl(1+\lambda^{d^i}+\lambda^{2d^i}+\dots+\lambda^{(d-1)d^i}\bigr)=\frac{1}{1-\lambda}$$
--   converges to $1/(1-\lambda)$.
--
--   Each natural number has a unique base-$d$ expansion, so expanding the product produces every power $\lambda^n$, $n\ge0$, exactly once, which gives the geometric series. In the paper the identity is used in logarithmic form, $\sum_{i\ge0}\log(1+\lambda^{d^i}+\dots+\lambda^{(d-1)d^i})=\log\frac{1}{1-\lambda}$, to compare $\sum_i\lambda^{d^i}$ with $\log\frac1{1-\lambda}$.
--
--   **Formalization Note.** The product is stated with Mathlib's `HasProd`, i.e. as an unconditionally convergent product (the finite products over finite sets of indices converge to $1/(1-\lambda)$); since every factor is at least $1$, this is equivalent to convergence of the partial products $\prod_{i<n}$. The $i$-th factor is $\sum_{k=0}^{d-1}\lambda^{k d^i}$.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1099, proof of Lemma 3, display

import Mathlib
import Definitions.Def_PowerTwoChoices_Asymptotics_ExpectedTime

open Filter Topology

namespace PowerTwoChoices.Asymptotics

/-- The product identity in the proof of Lemma 3 (Mitzenmacher 2001, p. 1099): for `d ≥ 2` and
`0 ≤ λ < 1`,
`∏_{i ≥ 0} (1 + λ^{d^i} + λ^{2 d^i} + ⋯ + λ^{(d-1) d^i}) = 1/(1 - λ)`,
stated as an (unconditionally) convergent infinite product (`HasProd`). -/
theorem product_identity (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    HasProd (fun i : ℕ => ∑ k ∈ Finset.range d, lam ^ (k * d ^ i)) (1 / (1 - lam)) := by sorry

end PowerTwoChoices.Asymptotics
