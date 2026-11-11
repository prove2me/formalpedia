-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_theorem_6_1
-- name    : TensorPCAGlauber.OddK.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:55:38.488135+00:00
-- url     : https://prove2.me/theorems/1cd8ab88-889e-4bcc-98ed-d2d79bbd4b70
-- title:
--   Theorem 6.1 (= Theorem 1.1) — averaged annealed Glauber dynamics achieves persistent strong recovery for odd $k$ whenever $\lambda\ge C_{\beta,k}N^{(k-2)/4}$
-- statement:
--   Let $k\ge3$ be odd. Observe $Y=\lambda\sqrt N(\theta^\star)^{\otimes k}+G$ with $G$ the symmetrized Gaussian $k$-tensor and an arbitrary fixed planted $x^\star\in\{\pm1\}^N$, and let $H(x)=N^{-(k-1)/2}\langle Y,x^{\otimes k}\rangle$. Run Algorithm 1 on $H$ from $\tilde X_0\sim\pi$ (independent of $G$), with first-phase inverse temperature $\beta_0$ and averaging time $T_{av}$ and second-phase inverse temperature $\beta$; let $(X_t)_{t\ge0}$ be the second-phase trajectory and $m(x)=N^{-1}\langle x^\star,x\rangle$.
--
--   There are $b>0$ and a function $A(a)>0$ for $a\in(0,b]$, chosen using only $k$, such that for every $\beta>0$ there are $C_{\beta,k},c_{\beta,k}>0$ independent of $a$. For every $a\in(0,b]$ the following holds (write $A=A(a)$). For every $\vartheta\in(0,1)$, $\eta\in(0,1/2)$ and $p>0$ there is $N_0$ such that for all $N\ge N_0$, all $x^\star$, all $\lambda\ge C_{\beta,k}N^{(k-2)/4}$, all $\beta_0\in[a,b]\cdot\lambda^{-1}N^{-k/2-\vartheta}$, all $T_{av}\ge AN^{2k+4\vartheta}$ and every deterministic $T$ with $T_{str}=\log N\le T\le N^p$,
--   $$P\Big[\inf_{t\in[T_{str},T]}m(X_t)\ge1-N^{-\eta}\Big]\ge1-\exp\Big(-c_{\beta,k}N^{\min\{(1-\vartheta)/2,\,1-2\eta\}}\Big),$$
--   the probability being joint over $G$, $\tilde X_0$ and the randomness of both phases. This is the paper's main result: a fully local Markov chain from a cold start reaches strong recovery at the conjectured algorithmic threshold $\lambda\asymp N^{(k-2)/4}$, below the cold-start barrier $N^{(k-2)/2}$ of fixed-temperature local chains.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - generalization: $T_{av}\asymp_kN^{2k+4\vartheta}$ → every $T_{av}\ge AN^{2k+4\vartheta}$, no upper bound; reason: $T_{av}$ enters only through Theorem 5.1, which needs only $T_{av}\gtrsim_k\beta_0^{-2}\lambda^{-2}N^{k+2\vartheta}\le a^{-2}N^{2k+4\vartheta}$; the printed band is a special case
--   - reading: $\beta_0\asymp_k\lambda^{-1}N^{-k/2-\vartheta}$, $C_{\beta,k}$ "sufficiently large", $c_{\beta,k}$ → $\exists b>0$ and $A:\mathbb R\to\mathbb R$ positive on $(0,b]$, depending only on $k$; then $\forall\beta>0$ $\exists C_{\beta,k},c_{\beta,k}>0$; then $\forall a\in(0,b]$, $\forall\vartheta,\eta,p$ $\exists N_0$; the averaging threshold is $A(a)N^{2k+4\vartheta}$; reason: Skolemizing the averaging constant keeps it independent of $\beta$ and keeps the signal and probability constants independent of $a$, as their printed subscripts require
--   - encoding: $T\le\mathrm{poly}(N)$; $\log$ → $\forall p>0$, $T\le N^p$; `Real.log` (natural logarithm); reason: the meaning of poly($N$); the paper's $\log$ is natural
--   - encoding: $P[\text{good event}]\ge 1-\varepsilon$ → the (outer) measure of the complementary bad event is $\le\varepsilon$; reason: equivalent for measurable events, and never weaker
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 37 (PDF 40), Theorem 6.1 (informal Theorem 1.1, p. 3, PDF 6)

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber
import Definitions.Def_TensorPCAGlauber_OddK_Algorithm1

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Theorem 6.1** (= Theorem 1.1; Persistent strong recovery above the algorithmic threshold).
Let `k ≥ 3` be odd and `β > 0`, and let `λ ≥ C_{β,k} N^{(k−2)/4}`. Fix `ϑ ∈ (0,1)`, `η ∈ (0,1/2)`;
let `(X_t)` be the second-phase trajectory of Algorithm 1 for `H(x) = N^{−(k−1)/2}⟨Y, x^{⊗k}⟩`,
started at `X̃_0 ∼ π`, with `β₀ ≍_k λ^{−1}N^{−k/2−ϑ}` and `T_av ≳_k N^{2k+4ϑ}`; `T_str = log N`.
For all large `N` and every deterministic `T_str ≤ T ≤ poly(N)`,
`P[inf_{t∈[T_str,T]} m(X_t) ≥ 1 − N^{−η}] ≥ 1 − exp(−c_{β,k} N^{min{(1−ϑ)/2, 1−2η}})`. -/
theorem theorem_6_1 (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k) :
    ∃ b : ℝ, 0 < b ∧ ∃ A : ℝ → ℝ,
    (∀ a : ℝ, 0 < a → a ≤ b → 0 < A a) ∧
    ∀ β : ℝ, 0 < β → ∃ Clam c : ℝ, 0 < Clam ∧ 0 < c ∧
    ∀ a : ℝ, 0 < a → a ≤ b →
    ∀ ϑ η p : ℝ, 0 < ϑ → ϑ < 1 → 0 < η → η < 1 / 2 → 0 < p →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (xstar : Cube N) (lam : ℝ),
      Clam * (N : ℝ) ^ (((k : ℝ) - 2) / 4) ≤ lam →
      ∀ β₀ : ℝ, a * (lam⁻¹ * (N : ℝ) ^ (-(k : ℝ) / 2 - ϑ)) ≤ β₀ →
        β₀ ≤ b * (lam⁻¹ * (N : ℝ) ^ (-(k : ℝ) / 2 - ϑ)) →
      ∀ Tav : ℝ, A a * (N : ℝ) ^ (2 * (k : ℝ) + 4 * ϑ) ≤ Tav →
      ∀ T : ℝ, Real.log N ≤ T → T ≤ (N : ℝ) ^ p →
        algMeasure k N
            {q | ∃ t ∈ Set.Icc (Real.log N) T,
                corr xstar (alg1Path (tpcaH k N lam xstar q.1) β₀ β Tav q.2.1 q.2.2.1 q.2.2.2 t)
                  < 1 - (N : ℝ) ^ (-η)}
          ≤ ENNReal.ofReal (Real.exp (-(c * (N : ℝ) ^ (min ((1 - ϑ) / 2) (1 - 2 * η))))) := by sorry

end TensorPCAGlauber.OddK
