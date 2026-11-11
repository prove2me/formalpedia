-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_lemma_6_9
-- name    : TensorPCAGlauber.OddK.lemma_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:55:35.530517+00:00
-- url     : https://prove2.me/theorems/492f9afe-9229-4e96-acfa-4bc40d5d8e5f
-- title:
--   Lemma 6.9 — under the null law, $\sup_{t\le T}|L_{null}m_\varphi(Y_t(e))|$ is $O(N^{-1/2})$ in exponential moment
-- statement:
--   Let $k\ge3$ be odd, $\beta>0$, $N\ge1$. Under the null law $Q$ (Definition 6.8), with $L_{null}=L_{H_{null},\beta}$ the generator for $H_{null}=\langle R,\cdot\rangle+W$ and $m_\varphi(y)=N^{-1}\langle\varphi,y\rangle$, for every $T>0$ and $e\in\Omega_N$,
--   $$E_Q\Big[\exp\Big(\frac N{16}\sup_{t\in[0,T]}\big|(L_{null}m_\varphi)(Y_t(e))\big|^2\Big)\Big]\le\sqrt2\,(1+NT).$$
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - encoding: $E_Q[\exp(\dots)]$ → lower Lebesgue integral `∫⁻` of `ENNReal.ofReal (exp …)` over the null driving measure, with the supremum taken in $[0,\infty]$; reason: no integrability side condition and no junk value
--   - encoding: $N$ a dimension → hypothesis $1\le N$ (or $N\ge N_0$); reason: excludes only zero dimension, where $N^{-1}$ and $t/N$ are undefined
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 47 (PDF 50), Lemma 6.9

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber
import Definitions.Def_TensorPCAGlauber_OddK_Gauge

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Lemma 6.9** (Uniform concentration along the null trajectory). Under the null law `Q`
(Definition 6.8), for every `T > 0` and `e ∈ Ω_N`,
`E_Q[exp((N/16) sup_{t∈[0,T]} |(L_null m_φ)(Y_t(e))|²)] ≤ √2 (1 + NT)`. -/
theorem lemma_6_9 (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k) (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 1 ≤ N)
    (T : ℝ) (hT : 0 < T) (e : Cube N) :
    ∫⁻ d, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp ((N : ℝ) / 16 *
          (generator (Hnull (nullEnv d).2.1 (nullEnv d).2.2) β (envCorr (nullEnv d).1)
            (glauberPath (Hnull (nullEnv d).2.1 (nullEnv d).2.2) β e d.2.2.2 t)) ^ 2)))
        ∂(nullDriveMeasure k N)
      ≤ ENNReal.ofReal (Real.sqrt 2 * (1 + N * T)) := by sorry

end TensorPCAGlauber.OddK
