-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_theorem_5_1
-- name    : TensorPCAGlauber.OddK.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:55:52.82996+00:00
-- url     : https://prove2.me/theorems/6632a1a5-f68f-446a-af30-a80c3ffbf3cb
-- title:
--   Theorem 5.1 — ergodic averaging recovers $\mathrm{sgn}(u_H)$ up to a vanishing Hamming fraction (odd $k$); a top eigenvector of $\bar\Sigma_{T_{av}}$ weakly recovers $x^\star$ (even $k$)
-- statement:
--   Let $k\ge3$. There are constants $C_k$ (threshold), $b_k$ (small), $A_k$ (large), $c_k,C'_k>0$, depending only on $k$, such that for every fixed $\vartheta\in(0,1)$ and all sufficiently large $N$: for every $x^\star$, every $\lambda\ge C_kN^{(k-2)/4}$, every $0<\beta_0\le b_k\lambda^{-1}N^{-k/2-\vartheta}$ and every $T_{av}\ge A_k\beta_0^{-2}\lambda^{-2}N^{k+2\vartheta}$, with $(\tilde X_t)$ Glauber dynamics for $H$ at $\beta_0$ started at $\tilde X_0\sim\pi$ independent of the Gaussian tensor, $\bar X_T=T^{-1}\int_0^T\tilde X_tdt$ and $\bar\Sigma_T=T^{-1}\int_0^T\tilde X_t\tilde X_t^\top dt$:
--
--   1. if $k$ is odd, with probability at least $1-\exp(-c_kN^{(1-\vartheta)/2})$,
--   $$\tfrac1Nd_H\big(\mathrm{sgn}(\bar X_{T_{av}}),\mathrm{sgn}(u_H)\big)\le\min\{N^{-\vartheta},\lambda^2\sigma_N^2N^{-\vartheta/2}\};$$
--   2. if $k$ is even, with probability at least $1-\exp(-c_kN)$, every top unit eigenvector $\hat v$ of $\bar\Sigma_{T_{av}}$ satisfies $|m(\mathrm{sgn}(\hat v))|\ge1-C'_k\big(N^{(k-2)/2}/\lambda^2+N^{-2\vartheta}\big)$.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - reading: "$0<\beta_0\lesssim_k\lambda^{-1}N^{-k/2-\vartheta}$ and $T_{av}\gtrsim_k\beta_0^{-2}\lambda^{-2}N^{k+2\vartheta}$ with sufficiently small and large implicit constants" → $\exists b_k,A_k>0$ (before $\vartheta$) with $\beta_0\le b_k\lambda^{-1}N^{-k/2-\vartheta}$ and $T_{av}\ge A_k\beta_0^{-2}\lambda^{-2}N^{k+2\vartheta}$; reason: both conditions are monotone, so "sufficiently small/large" is an existential threshold depending only on $k$
--   - reading: "$\hat v$ is a top unit eigenvector of $\bar\Sigma_{T_{av}}$" → the bound holds for every top unit eigenvector simultaneously; reason: a top eigenvector is not unique; the universal reading is the stronger one
--   - encoding: $P[\text{good event}]\ge 1-\varepsilon$ → the (outer) measure of the complementary bad event is $\le\varepsilon$; reason: equivalent for measurable events, and never weaker
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 27 (PDF 30), Theorem 5.1

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber
import Definitions.Def_TensorPCAGlauber_OddK_Algorithm1

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Theorem 5.1** (Recovery by ergodic averaging for tensor PCA). Let `λ ≥ C_k N^{(k−2)/4}` and
let `(X̃_t)` be Glauber dynamics for `H` at `β₀ > 0` with `X̃_0 ∼ π` independent of the Gaussian
tensor. For every fixed `ϑ ∈ (0,1)` and all large `N`, whenever `0 < β₀ ≤ b_k λ^{−1}N^{−k/2−ϑ}` and
`T_av ≥ A_k β₀^{−2}λ^{−2}N^{k+2ϑ}`: (1) for odd `k`, with probability `≥ 1 − exp(−c_k N^{(1−ϑ)/2})`,
`N^{−1} d_H(sgn(X̄_{T_av}), sgn(u_H)) ≤ min{N^{−ϑ}, λ²σ²_N N^{−ϑ/2}}`; (2) for even `k`, with
probability `≥ 1 − exp(−c_k N)`, every top unit eigenvector `v̂` of `Σ̄_{T_av}` has
`|m(sgn v̂)| ≥ 1 − C_k(N^{(k−2)/2}/λ² + N^{−2ϑ})`. -/
theorem theorem_5_1 (k : ℕ) (hk : 3 ≤ k) :
    ∃ Clam b A c C : ℝ, 0 < Clam ∧ 0 < b ∧ 0 < A ∧ 0 < c ∧ 0 < C ∧
    ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (xstar : Cube N) (lam : ℝ),
      Clam * (N : ℝ) ^ (((k : ℝ) - 2) / 4) ≤ lam →
      ∀ β₀ : ℝ, 0 < β₀ → β₀ ≤ b * lam⁻¹ * (N : ℝ) ^ (-(k : ℝ) / 2 - ϑ) →
      ∀ Tav : ℝ, A * (β₀ ^ 2)⁻¹ * (lam ^ 2)⁻¹ * (N : ℝ) ^ ((k : ℝ) + 2 * ϑ) ≤ Tav →
        (Odd k →
          phase1Measure k N
              {p | min ((N : ℝ) ^ (-ϑ)) (lam ^ 2 * sigmaSq k N * (N : ℝ) ^ (-ϑ / 2))
                  < (N : ℝ)⁻¹ * (hamming
                      (sgnCube (ergodicAvg (tpcaH k N lam xstar p.1) β₀ p.2.1 Tav p.2.2))
                      (sgnCube (avgGrad (tpcaH k N lam xstar p.1))) : ℝ)}
            ≤ ENNReal.ofReal (Real.exp (-(c * (N : ℝ) ^ ((1 - ϑ) / 2))))) ∧
        (Even k →
          phase1Measure k N
              {p | ∃ v : Fin N → ℝ,
                  IsTopUnitEigenvector
                    (ergodicSecondMoment (tpcaH k N lam xstar p.1) β₀ p.2.1 Tav p.2.2) v ∧
                  |corr xstar (sgnCube v)|
                    < 1 - C * ((N : ℝ) ^ (((k : ℝ) - 2) / 2) / lam ^ 2 + (N : ℝ) ^ (-2 * ϑ))}
            ≤ ENNReal.ofReal (Real.exp (-(c * N)))) := by sorry

end TensorPCAGlauber.OddK
