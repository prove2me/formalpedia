-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_lemma_3_10
-- name    : TensorPCAGlauber.OddK.lemma_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:54:33.137009+00:00
-- url     : https://prove2.me/theorems/fbc51e0c-58c7-4d44-b232-225b6a89197e
-- title:
--   Lemma 3.10 — Bernstein-type uniform concentration of Dynkin martingales of Glauber dynamics
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $(X_t)_{t\ge0}$ be continuous-time Glauber dynamics for a Hamiltonian $V:\Omega_N\to\mathbb R$ at inverse temperature $\beta\ge0$, with any initial law independent of the driving noise. Let $f:\Omega_N\to\mathbb R$ satisfy $\|f\|_{D^1}\le B$ and $\max_{x}\|\nabla_\Omega f(x)\|_\infty\le L$ with $B,L>0$, and let $M^f_t=f(X_t)-f(X_0)-\int_0^tL_{V,\beta}f(X_s)ds$ be its Dynkin martingale. Then for every $T,r>0$,
--   $$P\Big[\sup_{0\le t\le T}|M^f_t|\ge r\Big]\le2\exp\Big(-\frac{cNr^2}{B^2T+NLr}\Big).$$
--   This is the basic concentration tool for observables along the dynamics (Theorems 5.5, 6.2, 6.4).
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - reading: "the trajectory of Glauber dynamics" (initial state unspecified) → every initial law $\mu_0$ on $\Omega_N$, independent of the driving noise; reason: the source fixes no initial state; deterministic starts are the Dirac case
--   - encoding: $\sup_{0\le t\le T}|M^f_t|\ge r$ → `ENNReal.ofReal r ≤ ⨆ t ∈ [0,T], ENNReal.ofReal |M_t|`; reason: the supremum taken in $[0,\infty]$ is the true supremum, never a junk value
--   - encoding: $P[\text{good event}]\ge 1-\varepsilon$ → the (outer) measure of the complementary bad event is $\le\varepsilon$; reason: equivalent for measurable events, and never weaker
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 20 (PDF 23), Lemma 3.10

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Glauber

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Lemma 3.10** (Concentration of Dynkin martingales). There is a universal `c > 0` such that:
for Glauber dynamics `(X_t)` for any `V` at any `β ≥ 0` (initial law `μ₀` arbitrary, independent of
the driving noise), any `f` with `‖f‖_{D^1} ≤ B` and `max_x ‖∇_Ω f(x)‖_∞ ≤ L` (`B, L > 0`), and
every `T, r > 0`, `P[sup_{0≤t≤T} |M^f_t| ≥ r] ≤ 2 exp(−cNr²/(B²T + NLr))`. -/
theorem lemma_3_10 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) (V : Cube N → ℝ) (β : ℝ), 0 ≤ β →
      ∀ (μ₀ : Measure (Cube N)) [IsProbabilityMeasure μ₀]
        (f : Cube N → ℝ) (B L : ℝ), 0 < B → 0 < L → sobolevNorm 1 f ≤ B →
        (∀ x : Cube N, supNorm (grad f x) ≤ L) →
      ∀ T r : ℝ, 0 < T → 0 < r →
        (μ₀.prod (noiseMeasure N))
            {p | ENNReal.ofReal r ≤
              ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal |dynkinMart V β f p.1 p.2 t|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(c * N * r ^ 2 / (B ^ 2 * T + N * L * r)))) := by sorry

end TensorPCAGlauber.OddK
