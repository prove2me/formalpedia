-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_corollary_6_3
-- name    : TensorPCAGlauber.OddK.corollary_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:55:38.80999+00:00
-- url     : https://prove2.me/theorems/52fa73b0-00a9-4125-9c26-0a203bf72bf6
-- title:
--   Corollary 6.3 — Theorem 6.1's conclusion with $T_{str}=1+2\eta\log N$ when $\lambda\ge C_{\beta,k}N^{(k-2)/4+1/(4k)}$
-- statement:
--   Let $k\ge3$ be odd. There are $c_k,b_k,A_k>0$ and, for every $\beta>0$, a constant $C_{\beta,k}$ such that: for every $\vartheta\in(0,1)$, $\eta\in(0,1/2)$, $p>0$ and all sufficiently large $N$, every $x^\star$, every $\lambda\ge C_{\beta,k}N^{(k-2)/4+1/(4k)}$, every $\beta_0,T_{av}$ chosen as in Theorem 5.1 ($0<\beta_0\le b_k\lambda^{-1}N^{-k/2-\vartheta}$, $T_{av}\ge A_k\beta_0^{-2}\lambda^{-2}N^{k+2\vartheta}$), and every deterministic $T$ with $T_{str}=1+2\eta\log N\le T\le N^p$, the second-phase trajectory $(X_t)$ of Algorithm 1 for $H$, started at $\tilde X_0\sim\pi$, satisfies
--   $$P\Big[\inf_{t\in[T_{str},T]}m(X_t)\ge1-N^{-\eta}\Big]\ge1-\exp\Big(-c_kN^{\min\{(1-\vartheta)/2,\,1-2\eta\}}\Big).$$
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - reading: "$\gamma\ge(k-2)/4+1/(4k)$" with the §6 standing assumption $\lambda\ge C_{\beta,k}N^\gamma$ → $\lambda\ge C_{\beta,k}N^{(k-2)/4+1/(4k)}$; reason: the condition is monotone in $\gamma$
--   - reading: "$\beta_0$ and $T_{av}$ are chosen as in Theorem 5.1" → $\exists b_k,A_k$ with $0<\beta_0\le b_k\lambda^{-1}N^{-k/2-\vartheta}$, $T_{av}\ge A_k\beta_0^{-2}\lambda^{-2}N^{k+2\vartheta}$; reason: Theorem 5.1's sufficiently small/large constants
--   - encoding: $T\le\mathrm{poly}(N)$ → $\forall p>0$, $T\le N^p$; reason: the meaning of poly($N$)
--   - encoding: $P[\text{good event}]\ge 1-\varepsilon$ → the (outer) measure of the complementary bad event is $\le\varepsilon$; reason: equivalent for measurable events, and never weaker
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 41 (PDF 44), Corollary 6.3

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber
import Definitions.Def_TensorPCAGlauber_OddK_Algorithm1

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Corollary 6.3** (Persistent strong recovery slightly above the algorithmic threshold).
Odd `k ≥ 3`, `β > 0`, `λ ≥ C_{β,k}N^γ` with `γ ≥ (k−2)/4 + 1/(4k)`. Fix `ϑ ∈ (0,1)`, `η ∈ (0,1/2)`;
`β₀, T_av` as in Theorem 5.1; `T_str = 1 + 2η log N`. For all large `N` and every deterministic
`T_str ≤ T ≤ poly(N)`, the second phase `(X_t)` of Algorithm 1 from `X̃_0 ∼ π` satisfies
`P[inf_{t∈[T_str,T]} m(X_t) ≥ 1 − N^{−η}] ≥ 1 − exp(−c_k N^{min{(1−ϑ)/2, 1−2η}})`. -/
theorem corollary_6_3 (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k) :
    ∃ ck b A : ℝ, 0 < ck ∧ 0 < b ∧ 0 < A ∧
    ∀ β : ℝ, 0 < β → ∃ Cbk : ℝ, 0 < Cbk ∧
    ∀ ϑ η p : ℝ, 0 < ϑ → ϑ < 1 → 0 < η → η < 1 / 2 → 0 < p →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (xstar : Cube N) (lam : ℝ),
      Cbk * (N : ℝ) ^ (((k : ℝ) - 2) / 4 + 1 / (4 * (k : ℝ))) ≤ lam →
      ∀ β₀ : ℝ, 0 < β₀ → β₀ ≤ b * lam⁻¹ * (N : ℝ) ^ (-(k : ℝ) / 2 - ϑ) →
      ∀ Tav : ℝ, A * (β₀ ^ 2)⁻¹ * (lam ^ 2)⁻¹ * (N : ℝ) ^ ((k : ℝ) + 2 * ϑ) ≤ Tav →
      ∀ T : ℝ, 1 + 2 * η * Real.log N ≤ T → T ≤ (N : ℝ) ^ p →
        algMeasure k N
            {q | ∃ t ∈ Set.Icc (1 + 2 * η * Real.log N) T,
                corr xstar (alg1Path (tpcaH k N lam xstar q.1) β₀ β Tav q.2.1 q.2.2.1 q.2.2.2 t)
                  < 1 - (N : ℝ) ^ (-η)}
          ≤ ENNReal.ofReal (Real.exp (-(ck * (N : ℝ) ^ (min ((1 - ϑ) / 2) (1 - 2 * η))))) := by sorry

end TensorPCAGlauber.OddK
