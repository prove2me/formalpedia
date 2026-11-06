-- Prove2me | Theorems.Thm_RandomLPIPM_theorem_6_1
-- name    : RandomLPIPM.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:17.298671+00:00
-- url     : https://prove2.me/theorems/bd1798d7-7076-46b1-bbc3-c87d2bfd7d92
-- title:
--   Theorem 6.1 — projection bound over the entire path: $\le C_r(\log(ed))^{4.5}$ on $[a_d,1]$ with probability $1-d^{-r}$
-- statement:
--   Let $c\in(0,1/2]$, $cn\le d\le(1-c)n$, and $A\in\mathbb R^{d\times n}$ with independent $\mathcal N(0,1)$ entries; $(x_\mu,s_\mu)$ is the central path of LP(A). For every $r>0$ there is $C_r>0$, depending only on $r$ and $c$, such that for every $\kappa>0$ there is $d_0$ with the following property: for all $d\ge d_0$, all $n$ with $cn\le d\le(1-c)n$, and every deterministic $a_d\in[d^{-\kappa},1]$, with probability at least $1-d^{-r}$ over $A$,
--   $$\sup_{\mu\in[a_d,1]}\max\Big\{\|P(AX_\mu)\mathbf 1_n\|_\infty,\ \Big\|\frac{d\log x_\mu}{d\log\mu}\Big\|_\infty\Big\}\le C_r(\log(ed))^{4.5}.$$
--   The constant $C_r$ is independent of $\kappa$ and of $a_d$; only the dimension threshold depends on $\kappa$.
--
--   This is the uniform-in-$\mu$ bound that makes the central path of LP(A) polylog-Lipschitz in logarithmic coordinates down to $\mu=1/\operatorname{poly}(n)$, which is the hypothesis of Theorem 9.3.
--
--   Differences from the source:
--   - encoding: for all sufficiently large d (depending on r, κ, c) → ∃ d₀ after κ, for all d ≥ d₀; reason: the paper's quantifier order: C_r before κ and a_d
--   - encoding: ‖d log x_μ / d log μ‖_∞ ≤ C_r(log(ed))^4.5 → ∀ i ∃ g, HasDerivAt of t ↦ log x_{e^t, i} at log μ with |g| ≤ C_r(log(ed))^4.5; reason: asserts differentiability instead of using a junk-valued derivative
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
--   - encoding: x_μ the solution of the central path equations → x_μ the log-barrier minimizer; reason: equivalent by p.22
--   - encoding: P(M) := Mᵀ(MMᵀ)⁻¹M → orthogonal projector onto the row space of M; reason: equal for full-row-rank M, which AX_μ is almost surely
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 6.1, p.42

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_xMu
import Definitions.Def_RandomLPIPM_projRow
import Definitions.Def_ColumnRandLP_Norms

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Theorem 6.1 (Central-Path Conditioned Projection Bound over the Entire Path).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…),
Theorem 6.1, p.42.

Let `c ∈ (0, 1/2]`, `cn ≤ d ≤ (1 − c)n`, `A ∈ ℝ^{d×n}` with independent `N(0,1)` entries. Fix `κ > 0`
and deterministic `a_d ∈ [d^{−κ}, 1]`. For every fixed `r > 0` there is `C_r > 0`, depending only on
`r` and `c`, such that for all `d` large enough (depending on `r, κ, c`), with probability at least
`1 − d^{−r}` over `A`,
`sup_{μ ∈ [a_d, 1]} max{‖P(AX_μ)1‖_∞, ‖d log x_μ / d log μ‖_∞} ≤ C_r (log(ed))^{4.5}`.

**Formalization Note.** The quantifier order is the paper's: `C_r` is chosen before `κ` and `a_d`, so
it is independent of them; only the threshold `d₀` depends on `κ`. The bound on the logarithmic
derivative asserts its existence (`HasDerivAt` in `t = log μ`, coordinatewise). `log(ed)` is the
natural logarithm of `e·d`. The failure set is measured by the (outer) Gaussian measure. -/
theorem theorem_6_1 :
    ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ r : ℝ, 0 < r →
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ κ : ℝ, 0 < κ → ∃ d₀ : ℕ, ∀ d n : ℕ, d₀ ≤ d →
    c * n ≤ d → (d : ℝ) ≤ (1 - c) * n →
    ∀ a : ℝ, (d : ℝ) ^ (-κ) ≤ a → a ≤ 1 →
    GaussianMatrix.gaussianMatrix d n {A | ¬ ∀ μ ∈ Set.Icc a 1,
        ColumnRandLP.supNorm (projRow (Matrix.of A * diagonal (xMu (Matrix.of A) μ)) 1) ≤
          Cr * Real.log (Real.exp 1 * d) ^ (9 / 2 : ℝ) ∧
        ∀ i : Fin n, ∃ g : ℝ,
          HasDerivAt (fun t => Real.log (xMu (Matrix.of A) (Real.exp t) i)) g (Real.log μ) ∧
          |g| ≤ Cr * Real.log (Real.exp 1 * d) ^ (9 / 2 : ℝ)} ≤
      ENNReal.ofReal ((d : ℝ) ^ (-r)) := by sorry

end RandomLPIPM
