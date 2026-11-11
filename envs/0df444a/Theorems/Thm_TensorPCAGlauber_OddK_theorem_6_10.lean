-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_theorem_6_10
-- name    : TensorPCAGlauber.OddK.theorem_6_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:55:55.94358+00:00
-- url     : https://prove2.me/theorems/2c0cabdd-ee2b-49b7-84e7-e8175ad14ad9
-- title:
--   Theorem 6.10 — adaptive contiguity: planted probabilities of $\mathcal G_\tau$-events are bounded by null expectations weighted by the signal accumulated up to $\tau$
-- statement:
--   Let $k\ge3$ be odd, $\beta>0$, $N\ge1$. Fix $e\in\Omega_N$ and $T>0$, and let $(\mathcal G_t)_{0\le t\le T}$ be the joint filtration of the environment $(\varphi,R,W)$ and Glauber dynamics. Let $\tau$ be a $(\mathcal G_t)$-stopping time with $\tau\le T$ almost surely, and assume $\|\nabla_\Omega H_{sig}(Y_t(e))\|_\infty\le D$ for all $t<\tau$. Then for every $E\in\mathcal G_\tau$,
--   $$P(E)\le\exp\Big(\tfrac12N\lambda^2\sigma_N^2\Big)\,E_Q\Big[\exp\Big(\beta^2\cosh^2(\beta D)\int_0^\tau\|\nabla_\Omega H_{sig}(Y_t(e))\|^2dt\Big)\mathbf 1\{E\}\Big]^{1/2},$$
--   where $P$, $Q$ are the planted and null laws (Definitions 6.7–6.8).
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - generalization: $\lambda=C_{\beta,k}N^\gamma$ (§6.2 standing assumption) → every real $\lambda$; reason: the proof (Gaussian likelihood ratio and Girsanov tilt) uses no property of $\lambda$
--   - encoding: $P(E)$, $E_Q[\cdot]$ for laws on the canonical space → driving measure of the preimage under `plantedCanon`; `∫⁻` over the null driving measure composed with `nullCanon`; reason: avoids `Measure.map`; equal to the law's values
--   - encoding: $(\mathcal G_t)$-stopping time, $E\in\mathcal G_\tau$ → `τ : Canon N → ℝ≥0` with $\{\tau\le t\}\in\mathcal G_t$ for $t\in[0,T]$; $E\in\mathcal G_T$ and $E\cap\{\tau\le t\}\in\mathcal G_t$; reason: the standard definitions for a filtration on $[0,T]$
--   - reading: "$\tau\le T$ almost surely" → $Q[\tau>T]=0$; reason: $\{\tau>T\}\in\mathcal G_T$, on which $P\ll Q$, so this also gives $P[\tau>T]=0$; the proof applies optional stopping under $Q$
--   - reading: "assume $\|\nabla_\Omega H_{sig}(Y_t(e))\|_\infty\le D$ for all $t<\tau$" → for every point of the canonical space and every $0\le t<\tau$; reason: the assumption as printed, pathwise
--   - encoding: $N$ a dimension → hypothesis $1\le N$ (or $N\ge N_0$); reason: excludes only zero dimension, where $N^{-1}$ and $t/N$ are undefined
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 48 (PDF 51), Theorem 6.10

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber
import Definitions.Def_TensorPCAGlauber_OddK_Gauge

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Theorem 6.10** (Adaptive contiguity estimate). Fix `e ∈ Ω_N`, `T > 0`; let `(G_t)` be the
joint filtration of the environment `(φ, R, W)` and the dynamics, `τ` a `(G_t)`-stopping time with
`τ ≤ T` a.s., and assume `‖∇_Ω H_sig(Y_t(e))‖_∞ ≤ D` for all `t < τ`. Then for every `E ∈ G_τ`,
`P(E) ≤ exp(½Nλ²σ²_N) · E_Q[exp(β² cosh²(βD) ∫_0^τ ‖∇_Ω H_sig(Y_t(e))‖² dt) 1{E}]^{1/2}`. -/
theorem theorem_6_10 (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k) (β : ℝ) (hβ : 0 < β) (N : ℕ)
    (hN : 1 ≤ N) (lam : ℝ) (e : Cube N) (T : ℝ) (hT : 0 < T) (τ : Canon N → NNReal)
    (hτ : ∀ t ∈ Set.Icc (0 : ℝ) T, MeasurableSet[jointFiltration N t] {c | (τ c : ℝ) ≤ t})
    (hτT : nullDriveMeasure k N {d | T < (τ (nullCanon k N β e d) : ℝ)} = 0)
    (D : ℝ)
    (hD : ∀ (c : Canon N) (t : ℝ), 0 ≤ t → t < τ c →
      supNorm (grad (Hsig k N lam c.1.1) (canonPath e c t)) ≤ D)
    (E : Set (Canon N)) (hE : MeasurableSet[jointFiltration N T] E)
    (hEτ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      MeasurableSet[jointFiltration N t] (E ∩ {c | (τ c : ℝ) ≤ t})) :
    plantedDriveMeasure k N lam {d | plantedCanon k N lam β e d ∈ E}
      ≤ ENNReal.ofReal (Real.exp ((1 / 2) * N * lam ^ 2 * sigmaSq k N)) *
        (∫⁻ d, E.indicator
            (fun c => ENNReal.ofReal (Real.exp (β ^ 2 * Real.cosh (β * D) ^ 2 *
              ∫ t in (0 : ℝ)..(τ c : ℝ), eNorm (grad (Hsig k N lam c.1.1) (canonPath e c t)) ^ 2)))
            (nullCanon k N β e d) ∂(nullDriveMeasure k N)) ^ (1 / 2 : ℝ) := by sorry

end TensorPCAGlauber.OddK
