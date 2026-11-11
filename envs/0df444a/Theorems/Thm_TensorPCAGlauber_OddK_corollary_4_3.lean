-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_corollary_4_3
-- name    : TensorPCAGlauber.OddK.corollary_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:54:51.592069+00:00
-- url     : https://prove2.me/theorems/ba8f92eb-2380-4272-b953-1788967d0c1f
-- title:
--   Corollary 4.3 — the correlation of $\mathrm{sgn}(u_H)$ is $\Theta_k(\min\{1,\lambda N^{-(k-1)/4}\})$ w.h.p., and at least $N^{-1/4}$ above the threshold
-- statement:
--   Let $k\ge3$ be odd, $\lambda\ge0$, and $\hat u_H=\mathrm{sgn}(u_H)$. There are $c_k,C_k>0$ such that for every $N\ge1$ and every $x^\star$,
--   $$P\Big[c_k\min\{1,\lambda N^{-(k-1)/4}\}\le m(\hat u_H)\le C_k\min\{1,\lambda N^{-(k-1)/4}\}\Big]\ge1-2\exp\Big(-c_k\min\{N,\lambda^2N^{-(k-3)/2}\}\Big).$$
--   In particular there are $C_k,c_k>0$ such that if $\lambda\ge C_kN^{(k-2)/4}$ then, for all sufficiently large $N$, $P[m(\hat u_H)\ge N^{-1/4}]\ge1-\exp(-c_k\sqrt N)$. This is the warm start that Algorithm 1 approximates.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - reading: $c_k$ printed both as the factor of the lower bound and in the exponent → one constant $c$ for both; reason: equivalent: replace two constants by their minimum
--   - reading: "for all sufficiently large $N$" → $\exists N_0$ depending only on $k$, uniform in $\lambda$ and $x^\star$; reason: the threshold depends only on the constants of the statement
--   - encoding: $N$ a dimension → hypothesis $1\le N$ (or $N\ge N_0$); reason: excludes only zero dimension, where $N^{-1}$ and $t/N$ are undefined
--   - encoding: $P[\text{good event}]\ge 1-\varepsilon$ → the (outer) measure of the complementary bad event is $\le\varepsilon$; reason: equivalent for measurable events, and never weaker
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 24 (PDF 27), Corollary 4.3

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Corollary 4.3** (Correlation of the sign-rounded average discrete gradient). For odd
`k ≥ 3`, `λ ≥ 0` and `û_H = sgn(u_H)`:
`P[c_k min{1, λN^{−(k−1)/4}} ≤ m(û_H) ≤ C_k min{1, λN^{−(k−1)/4}}]
  ≥ 1 − 2 exp(−c_k min{N, λ² N^{−(k−3)/2}})`;
and if `λ ≥ C_k N^{(k−2)/4}` then for all large `N`, `P[m(û_H) ≥ N^{−1/4}] ≥ 1 − exp(−c_k √N)`. -/
theorem corollary_4_3 (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ N : ℕ, 1 ≤ N → ∀ lam : ℝ, 0 ≤ lam → ∀ xstar : Cube N,
        disorderMeasure k N
            {G' | ¬ (c * min 1 (lam * (N : ℝ) ^ (-((k : ℝ) - 1) / 4))
                      ≤ corr xstar (sgnCube (avgGrad (tpcaH k N lam xstar G'))) ∧
                    corr xstar (sgnCube (avgGrad (tpcaH k N lam xstar G')))
                      ≤ C * min 1 (lam * (N : ℝ) ^ (-((k : ℝ) - 1) / 4)))}
          ≤ ENNReal.ofReal
              (2 * Real.exp (-(c * min (N : ℝ) (lam ^ 2 * (N : ℝ) ^ (-((k : ℝ) - 3) / 2)))))) ∧
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ lam : ℝ, C * (N : ℝ) ^ (((k : ℝ) - 2) / 4) ≤ lam → ∀ xstar : Cube N,
        disorderMeasure k N
            {G' | corr xstar (sgnCube (avgGrad (tpcaH k N lam xstar G'))) < (N : ℝ) ^ (-(1 : ℝ) / 4)}
          ≤ ENNReal.ofReal (Real.exp (-(c * Real.sqrt N)))) := by sorry

end TensorPCAGlauber.OddK
