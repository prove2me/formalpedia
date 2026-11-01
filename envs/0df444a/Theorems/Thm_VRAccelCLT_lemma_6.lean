-- Prove2me | Theorems.Thm_VRAccelCLT_lemma_6
-- name    : VRAccelCLT.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:32.908069+00:00
-- url     : https://prove2.me/theorems/b3bb1b3a-c09c-4143-aec9-fafcd22a3a26
-- title:
--   Lemma 6: multivariate martingale CLT for triangular arrays
-- statement:
--   Let $\xi_{kt}$, $t=1,\dots,k$, $k\ge1$, be $m$-dimensional random vectors on one probability space, and set
--
--   $$
--   S_{kt}=\mathbb E[\xi_{kt}\xi_{kt}^T],\qquad R_{kt}=\mathbb E[\xi_{kt}\xi_{kt}^T\mid\xi_{k1},\dots,\xi_{k,t-1}],\qquad S_k=\sum_{t=1}^kS_{kt}.\tag{25}
--   $$
--
--   Assume
--
--   $$
--   \mathbb E[\xi_{kt}\mid\xi_{k1},\dots,\xi_{k,t-1}]=0,\qquad \sup_{k\ge1}\sum_{t=1}^k\mathbb E\big[\|\xi_{kt}\|^2\big]<\infty,\tag{26}
--   $$
--
--   $$
--   \lim_{k\to\infty}S_k=S,\qquad \lim_{k\to\infty}\sum_{t=1}^k\mathbb E\big[\|S_{kt}-R_{kt}\|\big]=0,\tag{27}
--   $$
--
--   $$
--   \lim_{k\to\infty}\sum_{t=1}^k\mathbb E\big[\|\xi_{kt}\|^2\,\mathbf 1[\|\xi_{kt}\|\ge\epsilon]\big]=0\qquad\text{for every }\epsilon>0.\tag{28}
--   $$
--
--   Then $\sum_{t=1}^k\xi_{kt}$ converges in distribution to $N(0,S)$ as $k\to\infty$.
--
--   This is the central limit theorem for martingale-difference arrays (conditional mean zero given the row's own past) with a Lindeberg condition; the paper cites it from [11, Lemma 3.3.1] and applies it in the proof of Lemma 7.
--
--   **Formalization Note** Each $\xi_{kt}$ is measurable. Matrix limits are entrywise and $\|S_{kt}-R_{kt}\|$ is the entrywise $\ell^1$ norm; all norms on matrices are equivalent, so (27) does not depend on the choice. (26) is a finite bound on lower Lebesgue integrals. $N(0,S)$ is Mathlib's multivariate Gaussian; $S$ is positive semidefinite as a limit of covariance sums, so this is not assumed.
--
--   Differences from the source:
--   - encoding: random vectors ξ_kt (measurability implicit) → each ξ_kt, 1 ≤ t ≤ k, measurable; reason: needed for the σ-algebras and expectations to be defined
--   - encoding: matrix norm ‖S_kt − R_kt‖ and matrix limit S_k → S → entrywise ℓ¹ norm Σ_{i,j}|·| and entrywise limits; reason: all norms on m × m matrices are equivalent
--   - encoding: sup_{k≥1} Σ_t E‖ξ_kt‖² < ∞ → ∃ C finite with Σ_t ∫⁻ ‖ξ_kt‖² ≤ C for all k ≥ 1; reason: same condition, stated without a real supremum
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Lemma 6, eqs. (25)–(28), p.14

import Mathlib
import Definitions.Def_VRAccelCLT_rowPast

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace VRAccelCLT

/-- **Lemma 6: CLT for martingale-difference triangular arrays.** Lei, Shanbhag,
arXiv:2006.07769v3, Lemma 6, p.14 (cited from [11, Lemma 3.3.1]): "Let ξkt, t = 1, · · · , k be
m-dimensional random vectors. Define Skt ≜ E[ξkt ξkt^T], Rkt ≜ E[ξkt ξkt^T | ξk1, · · · , ξk,t−1],
and Sk ≜ Σ_{t=1}^k Skt (25). Assume that E[ξkt | ξk1, · · · , ξk,t−1] = 0,
sup_{k≥1} Σ_{t=1}^k E[∥ξkt∥2] < ∞, (26) lim_{k→∞} Sk = S, lim_{k→∞} Σ_{t=1}^k E[∥Skt − Rkt∥] = 0,
(27) and lim_{k→∞} Σ_{t=1}^k E[∥ξkt∥2 I[∥ξkt∥≥ϵ]] = 0, ∀ϵ > 0. (28)
Then Σ_{t=1}^k ξkt →d N(0, S)."

The array is `ξ k t`, `1 ≤ t ≤ k`, of `ℝᵐ`-valued random vectors on one probability space; the
conditioning is on the row's own past `σ(ξ_{k1}, …, ξ_{k,t−1})` (`rowPast`).

**Formalization Note.** Each `ξ k t`, `1 ≤ t ≤ k`, is measurable (implicit in the paper); entries
outside this range are never used. (26) is stated with
lower Lebesgue integrals and a finite bound `C`. Matrix limits and the matrix norm of (27) are
entrywise: `‖S_kt − R_kt‖` is read as the entrywise `ℓ¹` norm `Σ_{i,j} |·|` (all norms on matrices are
equivalent, so (27) does not depend on the choice). `N(0, S)` is Mathlib's
`multivariateGaussian 0 S`; `S` is positive semidefinite as a limit of covariance sums, so no such
hypothesis is added. -/
theorem lemma_6 {m : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ξ : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ)
    (hmeas : ∀ k t, 1 ≤ t → t ≤ k → Measurable (ξ k t))
    (h26a : ∀ k t, 1 ≤ t → t ≤ k → μ[ξ k t | rowPast ξ k t] =ᵐ[μ] 0)
    (h26b : ∃ C : ℝ≥0, ∀ k, 1 ≤ k →
      ∑ t ∈ Finset.Icc 1 k, ∫⁻ ω, (‖ξ k t ω‖₊ : ℝ≥0∞) ^ 2 ∂μ ≤ C)
    (h27a : ∀ i j : Fin m,
      Tendsto (fun k => ∑ t ∈ Finset.Icc 1 k, ∫ ω, ξ k t ω i * ξ k t ω j ∂μ) atTop (𝓝 (S i j)))
    (h27b : Tendsto (fun k => ∑ t ∈ Finset.Icc 1 k, ∑ i : Fin m, ∑ j : Fin m,
        ∫ ω, |(∫ ω', ξ k t ω' i * ξ k t ω' j ∂μ) -
          (μ[fun ω' => ξ k t ω' i * ξ k t ω' j | rowPast ξ k t]) ω| ∂μ) atTop (𝓝 0))
    (h28 : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => ∑ t ∈ Finset.Icc 1 k,
        ∫ ω, Set.indicator {ω' | ε ≤ ‖ξ k t ω'‖} (fun ω' => ‖ξ k t ω'‖ ^ 2) ω ∂μ) atTop (𝓝 0)) :
    TendstoInDistribution (fun (k : ℕ) (ω : Ω) => ∑ t ∈ Finset.Icc 1 k, ξ k t ω) atTop id
      (fun _ => μ) (multivariateGaussian 0 S) := by sorry

end VRAccelCLT
