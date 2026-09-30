-- Prove2me | Theorems.Thm_TierneyMH_Peskun_vLam_tendsto_asymptotic_variance
-- name    : TierneyMH.Peskun.vLam_tendsto_asymptotic_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T12:45:44.209147+00:00
-- url     : https://prove2.me/theorems/b09bfdcc-a8e2-4040-9818-6de7a4570cc1
-- title:
--   $v_\lambda(f,H) \to v(f,H)$ as $\lambda \uparrow 1$
-- statement:
--   Let $\pi$ be a probability measure on a measurable space $E$, let $H$ be a Markov kernel reversible with respect to $\pi$, let $f \in L^2_0(\pi)$, and let $v = v(f,H) \in [0,\infty]$ be the asymptotic variance, i.e. the limit of $\frac1n \operatorname{Var}_H\bigl(\sum_{i=1}^n f(X_i)\bigr)$ for the chain started from $\pi$. Then
--
--   $$
--   v_\lambda(f, H) \;\longrightarrow\; v(f, H) \qquad \text{as } \lambda \uparrow 1,
--   $$
--
--   whether $v(f,H)$ is finite or infinite. Here $v_\lambda(f,H) = \langle f, f\rangle + 2\sum_{k\ge1}\lambda^k\langle f, H^k f\rangle$, the series form of $\langle f,(I-\lambda H)^{-1}(I+\lambda H)f\rangle$.
--
--   This reduces the comparison of asymptotic variances to a comparison of the regularized quantities $v_\lambda$ for each fixed $\lambda < 1$.
--
--   **Formalization Note** $v_\lambda$ is embedded in $[0,\infty]$ by $x \mapsto \max(x,0)$; since $v_\lambda(f,H) \ge 0$ for $0 \le \lambda < 1$ this loses nothing. The limit is along $\lambda \to 1$ from below. The asymptotic variance is supplied as the $[0,\infty]$-valued limit whose existence is the preceding milestone. The series form of $v_\lambda$ replaces the paper's operator form (see the definition of $v_\lambda$).
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 6, proof of Theorem 4 (v_λ(f, H) → v(f, H) as λ → 1)

import Mathlib
import Definitions.Def_TierneyMH_Peskun_chainMeasure
import Definitions.Def_TierneyMH_Peskun_vLam

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace TierneyMH.Peskun

/-- **Proof of Theorem 4** (Tierney 1998, p. 6), stated through the Neumann series of `vLam`.
Let `H` be a reversible Markov kernel with invariant distribution `π`, `f ∈ L²₀(π)`, and let
`v = v(f, H) ∈ [0, ∞]` be the limit of `(1/n) Var_H(∑_{i=1}^{n} f(X_i))` for the chain started
from `π`. Then `v_λ(f, H) → v(f, H)` as `λ ↑ 1`, whether `v(f, H)` is finite or infinite.
`v_λ(f, H) ≥ 0` for `0 ≤ λ < 1`, so its embedding `ENNReal.ofReal` into `[0, ∞]` loses
nothing on the relevant range. -/
theorem vLam_tendsto_asymptotic_variance {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hH : Kernel.IsReversible H π)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (v : ℝ≥0∞)
    (hv : Tendsto (fun n : ℕ => evariance (pathSum f n) (chainMeasure π H) / n)
      atTop (𝓝 v)) :
    Tendsto (fun lam : ℝ => ENNReal.ofReal (vLam π H f lam)) (𝓝[<] 1) (𝓝 v) := by sorry

end TierneyMH.Peskun
