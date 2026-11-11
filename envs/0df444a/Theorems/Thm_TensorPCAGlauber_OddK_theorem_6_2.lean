-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_theorem_6_2
-- name    : TensorPCAGlauber.OddK.theorem_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:54:30.3409+00:00
-- url     : https://prove2.me/theorems/5a628e1c-274d-45de-97a0-93a00f61fb65
-- title:
--   Theorem 6.2 — after critical correlation $m(X_t)\ge C\bar r_N$, the correlation exceeds $1-N^{-\eta}$ within $1+2\eta\log N$ and stays there up to $\mathrm{poly}(N)$
-- statement:
--   There is a universal $c>0$ such that for every odd $k\ge3$ there is $c_k>0$, and for every $\beta>0$ a constant $C_{\beta,k}>0$, with the following property. Fix $\eta,s\in(0,1/2)$, $C\ge1$ and $p>0$, and put $\bar r_N=N^{-s}$, $T_{str}=1+2\eta\log N$. For all sufficiently large $N$, every $x^\star$, every $\lambda$ with $\lambda\ge C_{\beta,k}N^{(k-2)/4}$ (the standing assumption of §6) and $\lambda\bar r_N^{k-1}\ge C_{\beta,k}$, every deterministic $T$ with $T_{str}\le T\le N^p$, and every initial state $X_0$ that is a measurable function of the Gaussian tensor and of randomness independent of the dynamics: with $(X_t)$ Glauber dynamics for $H$ at $\beta$ from $X_0$ and $\tau=\inf\{t\ge0:m(X_t)\ge C\bar r_N\}$,
--   $$P\Big[\tau<\infty\ \text{and}\ \inf_{t\in[T_{str},T]}m(X_{\tau+t})<1-N^{-\eta}\Big]\le e^{-c_kN}+2\exp\big(-cN\min\{\bar r_N^2,N^{-2\eta}\}\big).$$
--   This is the "boosting" step: critical correlation is upgraded to persistent strong recovery.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - reading: $P[\inf_{t\in[T_{str},T]}m(X_{\tau+t})\ge1-N^{-\eta}]\ge\dots$, with $X_{\tau+t}$ undefined when $\tau=\infty$ → the bad event is $\{\tau<\infty\}\cap\{\exists t\in[T_{str},T]:m(X_{\tau+t})<1-N^{-\eta}\}$; reason: the shifted path has meaning on $\{\tau<\infty\}$; for sufficiently large $N$, $C N^{-s}\le1$, and the finite-state Glauber chain has strictly positive flip rates, so this hitting time is finite almost surely under every initial law; the encoding preserves the printed probability
--   - reading: "any initial state $X_0$, possibly depending on $H$" → every $X_0=X_0(G',\omega')$ measurable in the Gaussian tensor and an auxiliary independent random element $\omega'$ of any probability space; reason: this is how §6.6 applies it ($X_0=\mathrm{sgn}(\bar X_{T_{av}})$)
--   - reading: §6 standing assumption $\lambda\ge C_{\beta,k}N^{\gamma}$, $\gamma\ge(k-2)/4$ → hypothesis $\lambda\ge C_{\beta,k}N^{(k-2)/4}$ with the same constant as in $\lambda\bar r_N^{k-1}\ge C_{\beta,k}$; reason: both are "sufficiently large" thresholds depending on $\beta,k$; one common constant is the larger of the two
--   - encoding: $T\le\mathrm{poly}(N)$ → $\forall p>0$, $T\le N^p$, with $N_0$ depending on $p$; reason: the meaning of poly($N$)
--   - encoding: $\tau\in[0,\infty]$ → `hitTime` is `ENNReal`-valued and $X_{\tau+t}$ uses `τ.toReal` on $\{\tau<\infty\}$; reason: no junk value of an empty infimum
--   - encoding: $P[\text{good event}]\ge 1-\varepsilon$ → the (outer) measure of the complementary bad event is $\le\varepsilon$; reason: equivalent for measurable events, and never weaker
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 38 (PDF 41), Theorem 6.2 (standing assumption p. 37, PDF 40)

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Theorem 6.2** (Persistent strong recovery after critical correlation). Odd `k ≥ 3`, `β > 0`,
`λ ≥ C_{β,k}N^{(k−2)/4}` (§6). Fix `η, s ∈ (0,1/2)`, `r̄_N = N^{−s}`, assume `λ r̄_N^{k−1} ≥ C_{β,k}`;
`τ = inf{t ≥ 0 : m(X_t) ≥ C r̄_N}` with `C ≥ 1`, `T_str = 1 + 2η log N`. For all large `N`, every
deterministic `T_str ≤ T ≤ poly(N)` and any initial state `X_0` (possibly depending on `H`), the
probability that `τ < ∞` and `m(X_{τ+t}) < 1 − N^{−η}` for some `t ∈ [T_str, T]` is at most
`exp(−c_k N) + 2 exp(−cN min{r̄_N², N^{−2η}})`. -/
theorem theorem_6_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 3 ≤ k → Odd k → ∃ ck : ℝ, 0 < ck ∧
    ∀ β : ℝ, 0 < β → ∃ Cbk : ℝ, 0 < Cbk ∧
    ∀ η s : ℝ, 0 < η → η < 1 / 2 → 0 < s → s < 1 / 2 → ∀ C : ℝ, 1 ≤ C → ∀ p : ℝ, 0 < p →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (xstar : Cube N) (lam : ℝ),
      Cbk * (N : ℝ) ^ (((k : ℝ) - 2) / 4) ≤ lam →
      Cbk ≤ lam * ((N : ℝ) ^ (-s)) ^ (k - 1) →
      ∀ T : ℝ, 1 + 2 * η * Real.log N ≤ T → T ≤ (N : ℝ) ^ p →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
        (X₀ : KTensor k N → Ω' → Cube N), Measurable (Function.uncurry X₀) →
        ((disorderMeasure k N).prod (μ'.prod (noiseMeasure N)))
            {q | hitTime (tpcaH k N lam xstar q.1) β (X₀ q.1 q.2.1) q.2.2 (corr xstar)
                    (C * (N : ℝ) ^ (-s)) < ⊤ ∧
                ∃ t ∈ Set.Icc (1 + 2 * η * Real.log N) T,
                  corr xstar (glauberPath (tpcaH k N lam xstar q.1) β (X₀ q.1 q.2.1) q.2.2
                    ((hitTime (tpcaH k N lam xstar q.1) β (X₀ q.1 q.2.1) q.2.2 (corr xstar)
                      (C * (N : ℝ) ^ (-s))).toReal + t)) < 1 - (N : ℝ) ^ (-η)}
          ≤ ENNReal.ofReal (Real.exp (-(ck * N))
              + 2 * Real.exp (-(c * N * min (((N : ℝ) ^ (-s)) ^ 2) ((N : ℝ) ^ (-2 * η))))) := by sorry

end TensorPCAGlauber.OddK
