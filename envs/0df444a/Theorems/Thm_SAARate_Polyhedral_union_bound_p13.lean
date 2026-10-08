-- Prove2me | Theorems.Thm_SAARate_Polyhedral_union_bound_p13
-- name    : SAARate.Polyhedral.union_bound_p13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:27.231023+00:00
-- url     : https://prove2.me/theorems/32f33337-d565-4e82-bc57-80c250fda250
-- title:
--   (3.18) and p. 13, proof of Theorem 3.2 — P(ℳ_N^c) ≤ Σ_i P(f̂_N(x_i) ≥ f(x_i)+ε) + Σ_j P(f̂_N(x_j) ≤ f(x_j)−ε)
-- statement:
--   Let $f$ and $\hat f_N$ be the true and sample average functions of the mission's setting, built on a sample $\omega^1,\omega^2,\dots$ defined on a probability space $(S,Q)$. Let $A$ and $A_N$ be their optimal sets on $\Theta$, and let
--   $$
--   \mathcal M_N:=\{\,A_N\text{ is nonempty and forms a face of }A\,\}.\tag{3.16}
--   $$
--   Let $x_1,\dots,x_q$ and $\ell$ be such that, for every sample path and every $N$, condition (2.13) $\hat f_N(x_i)<\hat f_N(x_j)$ ($i\le\ell<j$) implies $\mathcal M_N$, and such that $f(x_i)<f(x_j)$ for all $i\le\ell<j$. Then there is $\varepsilon>0$, not depending on $N$, with
--   $$
--   Q(\mathcal M_N^c)\le\sum_{i=1}^{\ell}Q\big(\hat f_N(x_i)\ge f(x_i)+\varepsilon\big)+\sum_{j=\ell+1}^{q}Q\big(\hat f_N(x_j)\le f(x_j)-\varepsilon\big)\quad\text{for every }N .
--   $$
--
--   The step combines (3.18), $\mathcal M_N^c\subseteq\{\exists\, i\le\ell<j:\ \hat f_N(x_i)\ge\hat f_N(x_j)\}$, with a union bound. It reduces the rate of Theorem 3.2 to the deviations of finitely many one-dimensional sample means.
--
--   **Formalization Note** The points are given through the hypotheses that Lemma 2.4 (c) provides. The standing assumptions (i)–(iv) are not needed for this step and are not assumed. $\mathcal M_N^c$ is not shown to be measurable, so $Q(\mathcal M_N^c)$ is its outer measure; an upper bound on it is the stronger statement. Indices are 0-based in Lean.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), pp. 12–13, proof of Theorem 3.2, (3.16), (3.18) and the display following it

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting

open MeasureTheory ProbabilityTheory

namespace SAARate.Polyhedral

/-- Proof of Theorem 3.2, (3.18) and p. 13: given points `x_1, …, x_q` for which condition (2.13)
forces `A_N` to be a nonempty face of `A` (Lemma 2.4 (c)) and `f(x_i) < f(x_j)` for
`i ≤ ℓ < j`, there is `ε > 0` (independent of `N`) with
`P(ℳ_N^c) ≤ Σ_{i ≤ ℓ} P(f̂_N(x_i) ≥ f(x_i) + ε) + Σ_{j > ℓ} P(f̂_N(x_j) ≤ f(x_j) − ε)`.
Indices are 0-based. Failure events are measured by the outer measure `Q`. -/
theorem union_bound_p13 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : SAARate.Sharp.E m → Ω → ℝ) (Θ : Set (SAARate.Sharp.E m))
    {S : Type*} [MeasurableSpace S] (Q : Measure S) (ω : ℕ → S → Ω)
    (q ℓ : ℕ) (x : Fin q → SAARate.Sharp.E m)
    (hc : ∀ (s : ℕ → Ω) (N : ℕ),
      (∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val → SAARate.Sharp.saaObj h s N (x i) < SAARate.Sharp.saaObj h s N (x j)) →
        (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h s N) Θ).Nonempty ∧
          IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h s N) Θ))
    (hgap : ∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val →
      SAARate.Sharp.expectedObj P h (x i) < SAARate.Sharp.expectedObj P h (x j)) :
    ∃ ε > 0, ∀ N : ℕ,
      Q {s | ¬ ((SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun k => ω k s) N) Θ).Nonempty ∧
          IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun k => ω k s) N) Θ))} ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < ℓ),
            Q {s | SAARate.Sharp.expectedObj P h (x i) + ε ≤ SAARate.Sharp.saaObj h (fun k => ω k s) N (x i)}) +
          ∑ j ∈ Finset.univ.filter (fun j : Fin q => ℓ ≤ j.val),
            Q {s | SAARate.Sharp.saaObj h (fun k => ω k s) N (x j) ≤ SAARate.Sharp.expectedObj P h (x j) - ε} := by sorry

end SAARate.Polyhedral
