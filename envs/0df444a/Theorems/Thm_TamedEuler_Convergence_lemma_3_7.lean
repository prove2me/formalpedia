-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_7
-- name    : TamedEuler.Convergence.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:32.436555+00:00
-- url     : https://prove2.me/theorems/cab69631-1d71-456c-a6f5-66b25b322ea7
-- title:
--   Lemma 3.7, p. 16 — time-continuous Burkholder–Davis–Gundy type inequality with constant p
-- statement:
--   Let $W$ be an $m$-dimensional standard $(\mathcal F_t)$-Brownian motion, $T>0$, $k\in\mathbb N$, and let $Z:[0,T]\times\Omega\to\mathbb R^{k\times m}$ be a predictable stochastic process with $\mathbb P\big[\int_0^T\|Z_s\|^2\,ds<\infty\big]=1$. Then
--   $$\Big\|\sup_{s\in[0,t]}\Big\|\int_0^sZ_u\,dW_u\Big\|\Big\|_{L^p(\Omega;\mathbb R)}\le p\Big(\int_0^t\sum_{i=1}^m\|Z_s\vec e_i\|^2_{L^p(\Omega;\mathbb R^k)}\,ds\Big)^{1/2}$$
--   for all $t\in[0,T]$ and all $p\in[2,\infty)$. Here $\|Y\|_{L^p(\Omega;\mathbb R^k)}=(\mathbb E\|Y\|^p)^{1/p}$ and $Z_s\vec e_i$ is the $i$-th column of $Z_s$.
--
--   This inequality bounds the stochastic-integral part of the error $X-\bar Y^N$ in the proof of Theorem 1.1.
--
--   **Formalization Note** The stochastic integral is the vector with components $\sum_j J_{ij}(s)$, where $J_{ij}$ is a continuous process related to the entry $Z^{(i,j)}$ (cut off to $0$ after $T$) and the coordinate $W^{(j)}$ by the published Brownian Itô-integral relation `EthierKurtz.HasBrownianItoIntegral` for the $\mathbb P$-completed filtration. That relation itself requires $\int_0^t(Z^{(i,j)}_s)^2ds<\infty$ on every path, which is stronger than the printed almost-sure condition (stated as well). Predictability is with respect to $(\mathcal F_t)$ (Mathlib's `IsStronglyPredictable`); the paper's filtration is complete, ours need not be, so this hypothesis is at least as strong as the printed one. The filtration is right-continuous, as in the standing setting. $\|Z_s\|$ is the operator norm. Both sides of the inequality are in $[0,\infty]$.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.7, (33)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_TamedEuler_Convergence_Setting
import Definitions.Def_TamedEuler_Convergence_Scheme
import Definitions.Def_EthierKurtz_completedSDEPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.7 (Time continuous
Burkholder–Davis–Gundy type inequality), (33): for `k ∈ ℕ` and a predictable process
`Z : [0,T] × Ω → ℝ^{k×m}` with `ℙ[∫_0^T ‖Z_s‖² ds < ∞] = 1`,
`‖sup_{s ∈ [0,t]} ‖∫_0^s Z_u dW_u‖‖_{L^p(Ω;ℝ)}
  ≤ p (∫_0^t Σ_{i=1}^m ‖Z_s e⃗_i‖²_{L^p(Ω;ℝ^k)} ds)^{1/2}`
for all `t ∈ [0,T]`, `p ∈ [2, ∞)`. The stochastic integral `∫_0^s Z_u dW_u ∈ ℝᵏ` has
components `Σ_j J_{ij}(s)`, where `J_{ij}` is a continuous version of the Brownian Itô
integral of the entry `Z^{(i,j)}` (cut off to `0` after `T`) against `W^{(j)}`, given by the
published relation `EthierKurtz.HasBrownianItoIntegral` for the `P`-completed filtration.
Note: that relation itself requires `∫_0^t (Z^{(i,j)}_s)² ds < ∞` on every path. -/
theorem lemma_3_7 {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (T : ℝ≥0) (hT : 0 < T) (hm : 1 ≤ m)
    (W : ℝ≥0 → Ω → SDEState m) (hW : SabanisEuler.Shared.IsWienerMartingale P ℱ W)
    (k : ℕ) (hk : 1 ≤ k)
    (Z : ℝ≥0 → Ω → Matrix (Fin k) (Fin m) ℝ) (hZ : IsStronglyPredictable ℱ Z)
    (hZfin : ∀ᵐ ω ∂P,
      ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (opNorm (Z s.toNNReal ω) ^ 2) < ∞)
    (J : ℝ≥0 → Ω → Fin k → Fin m → ℝ)
    (hJcont : ∀ ω i j, Continuous (fun s => J s ω i j))
    (hJ : ∀ i j, HasBrownianItoIntegral P (completedSDEPast P ℱ) (fun t ω => W t ω j)
      (fun t ω => if t ≤ T then Z t ω i j else 0) (fun t ω => J t ω i j)) :
    ∀ t : ℝ≥0, t ≤ T → ∀ p : ℝ, 2 ≤ p →
      (∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ≥0) t,
          ‖(WithLp.toLp 2 (fun i => ∑ j, J s ω i j) : SDEState k)‖ₑ) ^ p ∂P) ^ (1 / p)
        ≤ ENNReal.ofReal p *
          (∫⁻ s in Set.Icc (0 : ℝ) t, ∑ i : Fin m,
            eLpNorm (fun ω => column (Z s.toNNReal ω) i) (ENNReal.ofReal p) P ^ 2)
            ^ (1 / 2 : ℝ) := by sorry

end TamedEuler.Convergence
