-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_theorem_6_4
-- name    : TensorPCAGlauber.OddK.theorem_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:55:59.865218+00:00
-- url     : https://prove2.me/theorems/3f9d5687-0aaa-44bb-8c1d-effbb3bd4232
-- title:
--   Theorem 6.4 — simultaneously from every start in a small Hamming ball around $\mathrm{sgn}(u_H)$, Glauber dynamics reaches correlation $Cr_N$ within time $C_1N^{-(k-1)(\gamma-(k-2)/4)}$
-- statement:
--   Let $k\ge3$ be odd, $\beta>0$, $C>0$. There are $C_1,c>0$ depending only on $\beta,k,C$, and a threshold $C_0$, such that for every $C_{\beta,k}\ge C_0$ and every $\vartheta\in(0,1/2)$ the following holds for all sufficiently large $N$, every $\gamma$ with $(k-2)/4\le\gamma\le(k-2)/4+1/(4k)$ and every $x^\star$. Put $\lambda=C_{\beta,k}N^\gamma$, $r_N=\lambda^{-1/(k-1)}$, $u_H=E_\pi[\nabla_\Omega H]$, and for $e\in\Omega_N$ let $(X_t(e))$ be Glauber dynamics for $H$ at $\beta$ from $e$ and $T_*(e)=\inf\{t\ge0:m(X_t(e))\ge Cr_N\}$. Then
--   $$P\Big[T_*(e)\le C_1N^{-(k-1)(\gamma-(k-2)/4)}\ \ \forall e\in B_H\big(\mathrm{sgn}(u_H),\lambda^2\sigma_N^2N^{-\vartheta}\big)\Big]\ge1-\exp\big(-cN\lambda^2\sigma_N^2\big).$$
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - reading: "$\lambda=C_{\beta,k}N^\gamma$, $C_{\beta,k}$ a sufficiently large constant" (depending on $\beta,k,C$) → $\exists C_0$, $\forall C_{\beta,k}\ge C_0$, with $N_0$ uniform over $\gamma$ in the closed range; reason: "sufficiently large" as a threshold; uniformity in $\gamma$ is what §6.6 uses when $\gamma$ varies with $N$
--   - reading: $X_t(e)$ for all $e$ on one probability space → all starts driven by the same noise (natural coupling); reason: the source leaves the coupling implicit; this is the coupling of "Glauber dynamics from $e$" as a function of the noise
--   - encoding: $T_*(e)=\inf\{\dots\}$ → `hitTime` in $[0,\infty]$ ($\infty$ if never reached); reason: no junk value of an empty infimum
--   - encoding: $P[\text{good event}]\ge 1-\varepsilon$ → the (outer) measure of the complementary bad event is $\le\varepsilon$; reason: equivalent for measurable events, and never weaker
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 42 (PDF 45), Theorem 6.4 (setting §6.2, p. 42; constants p. 51, PDF 54)

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber
import Definitions.Def_TensorPCAGlauber_OddK_Algorithm1

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Theorem 6.4** (Critical recovery from a sufficiently warm start). Odd `k ≥ 3`, `β > 0`,
`λ = C_{β,k}N^γ` with `(k−2)/4 ≤ γ ≤ (k−2)/4 + 1/(4k)` and `C_{β,k}` sufficiently large,
`r_N = λ^{−1/(k−1)}`. Fix `ϑ ∈ (0,1/2)` and, for every `e`, `T_*(e) = inf{t ≥ 0 : m(X_t(e)) ≥ C r_N}`.
For all large `N`,
`P[T_*(e) ≤ C₁ N^{−(k−1)(γ−(k−2)/4)} ∀ e ∈ B_H(sgn(u_H), λ²σ²_N N^{−ϑ})] ≥ 1 − exp(−cNλ²σ²_N)`,
with `C₁, c > 0` depending only on `β, k, C`. -/
theorem theorem_6_4 (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k) (β : ℝ) (hβ : 0 < β) (C : ℝ)
    (hC : 0 < C) :
    ∃ C₁ c : ℝ, 0 < C₁ ∧ 0 < c ∧ ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Cbk : ℝ, C₀ ≤ Cbk →
    ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ γ : ℝ, ((k : ℝ) - 2) / 4 ≤ γ → γ ≤ ((k : ℝ) - 2) / 4 + 1 / (4 * (k : ℝ)) →
    ∀ xstar : Cube N,
      disorderNoiseMeasure k N
          {q | ¬ ∀ e ∈ hammingBall
                  (sgnCube (avgGrad (tpcaH k N (Cbk * (N : ℝ) ^ γ) xstar q.1)))
                  ((Cbk * (N : ℝ) ^ γ) ^ 2 * sigmaSq k N * (N : ℝ) ^ (-ϑ)),
                hitTime (tpcaH k N (Cbk * (N : ℝ) ^ γ) xstar q.1) β e q.2 (corr xstar)
                    (C * (Cbk * (N : ℝ) ^ γ) ^ (-(1 : ℝ) / ((k : ℝ) - 1)))
                  ≤ ENNReal.ofReal (C₁ * (N : ℝ) ^ (-((k : ℝ) - 1) * (γ - ((k : ℝ) - 2) / 4)))}
        ≤ ENNReal.ofReal (Real.exp (-(c * N * (Cbk * (N : ℝ) ^ γ) ^ 2 * sigmaSq k N))) := by sorry

end TensorPCAGlauber.OddK
