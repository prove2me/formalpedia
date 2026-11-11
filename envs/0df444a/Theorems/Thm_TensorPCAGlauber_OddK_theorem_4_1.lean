-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_theorem_4_1
-- name    : TensorPCAGlauber.OddK.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:54:21.356544+00:00
-- url     : https://prove2.me/theorems/d1087723-2f28-498b-bce6-569ca3b4b14e
-- title:
--   Theorem 4.1 — signal-noise decomposition of the average discrete gradient ($u_H=0$ for even $k$; $u_H=N\lambda\alpha_N\theta^\star+\zeta$, $\zeta\sim N(0,\sigma_N^2I)$ for odd $k$)
-- statement:
--   Let $H$ be the tensor PCA Hamiltonian (eq. (3)) and $u_H=E_\pi[\nabla_\Omega H]$. (1) If $k$ is even, then $u_H=0$ for every realization of the Gaussian tensor, every $\lambda$ and every $x^\star$. (2) If $k$ is odd, then there are $c_k,C_k>0$ such that for every $N\ge1$
--   $$u_H=N\lambda\alpha_N\theta^\star+\zeta,\qquad \zeta=E_\pi[xH_0(x)]\sim N(0,\sigma_N^2I),$$
--   with $c_kN^{-k/2}\le\alpha_N\le C_kN^{-k/2}$, $\sigma_N^2=\alpha_N\sqrt N$ and $c_kN^{-(k-1)/2}\le\sigma_N^2\le C_kN^{-(k-1)/2}$. Here $\alpha_N$ and $\sigma_N^2$ are the explicit quantities (18)–(19). For odd $k$ the average gradient is thus a noisy observation of the planted vector with signal-to-noise ratio $\lambda\sigma_N\asymp_k\lambda N^{-(k-1)/4}$.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - reading: "$u_H=N\lambda\alpha_N\theta^\star+\zeta$ where $\alpha_N\asymp_kN^{-k/2}$" → $\alpha_N$ is the explicit quantity of eq. (18); reason: the proof defines $\alpha_N$ by (18); the decomposition then pins it down
--   - encoding: $\zeta\doteq E_\pi[xH_0(x)]$ → `zeta` is $E_\pi[\nabla_\Omega H_0]$ (Lemma 6.5) and a conjunct asserts it equals $E_\pi[xH_0(x)]$; reason: one shared definition for both appearances of $\zeta$; the conjunct restores the printed definition
--   - encoding: $\zeta\sim N(0,\sigma_N^2I)$ → `(disorderMeasure k N).map zeta = Measure.pi (fun _ => gaussianReal 0 σ²_N)`; reason: the law of $\zeta$ as a product of centered Gaussians, i.e. $N(0,\sigma_N^2I)$
--   - encoding: $N$ a dimension → hypothesis $1\le N$ (or $N\ge N_0$); reason: excludes only zero dimension, where $N^{-1}$ and $t/N$ are undefined
--   - generalization: $\lambda\ge0$ in the tensor PCA model → every real $\lambda$; reason: the decomposition is linear in the signal strength, the even-parity identity holds for every real signal strength, and the noise law is independent of it; all source instances are retained
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 22 (PDF 25), Theorem 4.1

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Theorem 4.1** (Signal-noise decomposition of the average discrete gradient). Let
`u_H = E_π[∇_Ω H]`. (1) If `k` is even, `u_H = 0` deterministically. (2) If `k` is odd,
`u_H = Nλα_N θ⋆ + ζ` with `ζ = E_π[x H_0(x)] ∼ N(0, σ²_N I)`, `α_N ≍_k N^{−k/2}` and
`σ²_N = α_N √N ≍_k N^{−(k−1)/2}`. -/
theorem theorem_4_1 (k : ℕ) (hk : 3 ≤ k) :
    (Even k → ∀ (N : ℕ) (lam : ℝ) (xstar : Cube N) (G' : KTensor k N),
        avgGrad (tpcaH k N lam xstar G') = 0) ∧
    (Odd k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        (∀ (lam : ℝ) (xstar : Cube N) (G' : KTensor k N),
          avgGrad (tpcaH k N lam xstar G')
            = fun i => N * lam * alphaN k N * thetaStar xstar i + zeta k N G' i) ∧
        (∀ G' : KTensor k N, zeta k N G' = fun i => avg fun x => vec x i * H0 k N G' x) ∧
        (disorderMeasure k N).map (zeta k N)
          = Measure.pi (fun _ : Fin N => gaussianReal 0 (sigmaSq k N).toNNReal) ∧
        c * (N : ℝ) ^ (-(k : ℝ) / 2) ≤ alphaN k N ∧
        alphaN k N ≤ C * (N : ℝ) ^ (-(k : ℝ) / 2) ∧
        sigmaSq k N = alphaN k N * Real.sqrt N ∧
        c * (N : ℝ) ^ (-((k : ℝ) - 1) / 2) ≤ sigmaSq k N ∧
        sigmaSq k N ≤ C * (N : ℝ) ^ (-((k : ℝ) - 1) / 2)) := by sorry

end TensorPCAGlauber.OddK
