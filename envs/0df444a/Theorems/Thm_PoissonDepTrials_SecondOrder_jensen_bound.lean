-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_jensen_bound
-- name    : PoissonDepTrials.SecondOrder.jensen_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:52:35.936851+00:00
-- url     : https://prove2.me/theorems/600c00ae-e449-4def-afc8-a5d1a97ea3a0
-- title:
--   Proof of Theorem 5.1, p. 545 — λ^{−1}Σ_i p_i²Σ_{j≠i} p_j²/λ^{(i)} ≤ 2^½λ^{−1}Σp_i³ when max p_i ≤ λ/2
-- statement:
--   Let $p_1,\dots,p_n\ge0$ with $\lambda=\sum_{i=1}^np_i>0$ and $\max_ip_i\le\lambda/2$, and put $\lambda^{(i)}=\sum_{j\ne i}p_j$. Then
--   $$\lambda^{-1}\sum_{i=1}^np_i^2\sum_{j\ne i}\frac{p_j^2}{\lambda^{(i)}}\le2^{1/2}\lambda^{-1}\sum_{i=1}^np_i^3.$$
--
--   This is the first and last member of the chain of inequalities that closes the proof of Theorem 5.1 (the page derives it with Jensen's inequality); it converts the second term of (5.9) into a multiple of $\lambda^{-1}\sum p_i^3$.
--
--   **Formalization Note** The statement is purely about the numbers $p_i$ and is formalized for arbitrary nonnegative reals satisfying the page's hypothesis $\max p_i\le\lambda/2$; this contains the case $p_i=P(X_i=1)$ used in the paper. $\lambda>0$ is added because the chain divides by $\lambda^{(i)}$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 545, proof of Theorem 5.1 (Jensen chain after (5.9))

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- The Jensen chain closing the proof of Theorem 5.1, p. 545 (first and last members), for
arbitrary nonnegative reals `p_1, …, p_n` with `λ = Σ p_i > 0` and `max p_i ≤ λ/2`:
`λ^{−1} Σ_i p_i² Σ_{j≠i} p_j²/λ^{(i)} ≤ 2^{1/2} λ^{−1} Σ_i p_i³`, where `λ^{(i)} = Σ_{j≠i} p_j`. -/
theorem jensen_bound (n : ℕ) (p : ℕ → ℝ) (hp : ∀ i ∈ Finset.Icc 1 n, 0 ≤ p i)
    (hlam : 0 < ∑ i ∈ Finset.Icc 1 n, p i)
    (hpbar : ∀ i ∈ Finset.Icc 1 n, p i ≤ (∑ k ∈ Finset.Icc 1 n, p k) / 2) :
    (∑ k ∈ Finset.Icc 1 n, p k)⁻¹ * ∑ i ∈ Finset.Icc 1 n, p i ^ 2 *
        ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
          p j ^ 2 / ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i), p k ≤
      Real.sqrt 2 * (∑ k ∈ Finset.Icc 1 n, p k)⁻¹ * ∑ i ∈ Finset.Icc 1 n, p i ^ 3 := by sorry

end PoissonDepTrials.SecondOrder
