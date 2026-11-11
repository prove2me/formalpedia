-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_theorem_5_5
-- name    : TensorPCAGlauber.OddK.theorem_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:54:29.874544+00:00
-- url     : https://prove2.me/theorems/2194ba48-5f97-42ec-98ad-7056e61e5f97
-- title:
--   Theorem 5.5 — the ergodic average of high-temperature Glauber dynamics approximates $\beta_0E_\pi[\nabla_\Omega V]$ when $\|V\|_{D^2}\le BN$
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $V:\Omega_N\to\mathbb R$ satisfy $\|V\|_{D^2}\le BN$ for some $B>0$, let $(Z_t)$ be Glauber dynamics for $V$ at inverse temperature $\beta_0\ge0$ with $Z_0\sim\pi$, and $\bar Z_T=T^{-1}\int_0^TZ_tdt$. For every $T>0$ and $\delta\in(0,1)$, with probability at least $1-\delta$,
--   $$\big\|\bar Z_T-\beta_0E_\pi[\nabla_\Omega V]\big\|\le C\Big[(1+\beta_0B)\Big(\sqrt{\tfrac{N+\log(1/\delta)}T}+\tfrac{N+\log(1/\delta)}T\Big)+\beta_0^2B^2\sqrt N+\beta_0^3B^3N^{3/2}\Big].$$
--   The norm is Euclidean. The first terms quantify the long-time limit, the last two the high-temperature expansion.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - encoding: "$\lesssim$ with universal implicit constant" → $\exists C>0$ before every other quantifier; reason: the constant is universal
--   - encoding: $P[\text{good event}]\ge 1-\varepsilon$ → the (outer) measure of the complementary bad event is $\le\varepsilon$; reason: equivalent for measurable events, and never weaker
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 31 (PDF 34), Theorem 5.5 (setting p. 30, PDF 33)

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Theorem 5.5** (Recovery of the average discrete gradient). There is a universal `C > 0` such
that: if `‖V‖_{D^2} ≤ BN` (`B > 0`), `(Z_t)` is Glauber dynamics for `V` at `β₀ ≥ 0` with
`Z_0 ∼ π`, and `Z̄_T = T^{−1}∫_0^T Z_t dt`, then for every `T > 0` and `δ ∈ (0,1)`, with
probability at least `1 − δ`,
`‖Z̄_T − β₀ E_π[∇_Ω V]‖ ≤ C[(1 + β₀B)(√((N + log(1/δ))/T) + (N + log(1/δ))/T)
  + β₀²B²√N + β₀³B³N^{3/2}]`. -/
theorem theorem_5_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (V : Cube N → ℝ) (B : ℝ), 0 < B → sobolevNorm 2 V ≤ B * N →
      ∀ β₀ : ℝ, 0 ≤ β₀ → ∀ T δ : ℝ, 0 < T → 0 < δ → δ < 1 →
        ((piMeasure N).prod (noiseMeasure N))
            {p | C * ((1 + β₀ * B) * (Real.sqrt ((N + Real.log (1 / δ)) / T)
                    + (N + Real.log (1 / δ)) / T)
                  + β₀ ^ 2 * B ^ 2 * Real.sqrt N + β₀ ^ 3 * B ^ 3 * (N : ℝ) ^ ((3 : ℝ) / 2))
                < eNorm (fun i => ergodicAvg V β₀ p.1 T p.2 i - β₀ * avgGrad V i)}
          ≤ ENNReal.ofReal δ := by sorry

end TensorPCAGlauber.OddK
