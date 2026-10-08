-- Prove2me | Theorems.Thm_PrimalDualLDR_Multistage_theorem_3
-- name    : PrimalDualLDR.Multistage.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:21.281019+00:00
-- url     : https://prove2.me/theorems/239cdf55-7681-415a-9f24-492aa4c9e33f
-- title:
--   Theorem 3 — in multistage programs, 𝓜𝒮𝒫^u and 𝓜𝒮𝒫^l are equivalent to the linear programs (4.2) and (4.6)
-- statement:
--   Consider a linear multistage stochastic program $\mathcal{MSP}$ (p. 18): over $T$ stages, minimize $\mathbb E\big(\sum_t c_t(\xi^t)^\top x_t(\xi^t)\big)$ over non-anticipative rules $x_t \in \mathcal L^2_{k^t,n_t}$ subject to $\mathbb E_t\big(\sum_s A_{ts}x_s(\xi^s)\big) \le b_t(\xi^t)$ $\mathbb P$-a.s., with deterministic constraint matrices $A_{ts}$, $c_t(\xi^t) = C_tP_t\xi$ and $b_t(\xi^t) = B_tP_t\xi$.
--
--   Assume that $\mathbb P$ has a polyhedral support $\Xi = \{\xi : W\xi \ge h\}$ of the type (2.1) — nonempty, bounded, spanning $\mathbb R^k$, with $W, h$ of the form (2.1b) and $k_1 = 1$ — while
--   $$\mathbb E_t(\xi) = M_tP_t\xi \quad \mathbb P\text{-a.s. for some } M_t \in \mathbb R^{k\times k^t},\ t \in \mathbb T.$$
--   If $\mathcal{MSP}$ is strictly feasible, then $\mathcal{MSP}^u$ and $\mathcal{MSP}^l$ are equivalent to the linear programs (4.2) and (4.6), respectively; the second equivalence is stated under the condition $(\star)$: $k \ge 2$, or some row of $\hat W$ is nonzero (see the Formalization Note):
--   $$\mathrm{val}(\mathcal{MSP}^u) = \mathrm{val}(4.2) \qquad\text{and}\qquad (\star) \implies \mathrm{val}(\mathcal{MSP}^l) = \mathrm{val}(4.6).$$
--
--   Since $\mathcal{MSP}^u$ is a conservative and $\mathcal{MSP}^l$ a progressive approximation of $\mathcal{MSP}$, the two linear programs bracket the optimal value of the multistage program, and both are of size polynomial in the problem dimensions.
--
--   **Formalization Note** "Equivalent" is formalized as equality of optimal values, each the infimum of the objective over the feasible set in the extended reals ($+\infty$ when infeasible, $-\infty$ when unbounded). The matrices $M_t$ are data of the setting and the hypothesis states that they give the conditional mean; this is equivalent to the paper's "for some $M_t$", since the problems depend on $M_t$ only through $M_tP_t\xi$ on $\Xi$. Strict feasibility of $\mathcal{MSP}$, which §4 does not define, is the analogue of (2.9) for the standard form (4.1): slacks bounded below by some $\varepsilon > 0$. The equality constraint of $\mathcal{MSP}^l$ is in the corrected reading in which $\sum_s$ covers only $A_{ts}x_s(\xi^s)$. The final sentence of the printed theorem (the linear programs have polynomial size and are efficiently solvable) is informal and not formalized. The hypothesis $(\star)$ on the second equality is a repair and is not in the paper (the first equality is stated without it, as printed): for $k = 1$ the support is $\Xi = \{1\}$, and if $W$ has no nonzero row besides the two rows of (2.1b), the cone $\mathcal K = \{z : (W - he_1^\top)z \ge 0\}$ of Proposition 3 is all of $\mathbb R$ while $\mathcal K_{\mathbb P} = [0,\infty)$, so Proposition 3 and the second equality fail. For instance $T = 1$, $n_1 = m_1 = 1$, $A_{11} = 1$, $B_1 = 0$, $C_1 = -1$ is strictly feasible, $\mathcal{MSP}^l$ has value $0$, and (4.6) is unbounded below. For $k \ge 2$ the spanning support has at least two points and the omitted constraint $e_1^\top z \ge 0$ is implied by $(W - he_1^\top)z \ge 0$, as the paper's argument (p. 8) needs; for $k = 1$ with a nonzero row $\hat w$ of $\hat W$ (then $\hat w > 0$, as $\Xi = \{1\}$ is nonempty), $\mathcal K = [0,\infty) = \mathcal K_{\mathbb P}$ as well. So $(\star)$ excludes exactly the case in which the printed statement fails.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 22, Theorem 3

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting
import Definitions.Def_PrimalDualLDR_Multistage_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.Multistage

/-- Theorem 3 (p. 22): assume that `P` has a polyhedral support of the type (2.1), while
`𝔼_t(ξ) = M_t P_t ξ` almost surely for the matrices `M_t ∈ ℝ^{k × k^t}`, `t ∈ 𝕋`. If `𝓜𝒮𝒫` (which has
deterministic constraint matrices `A_ts` by construction) is strictly feasible, then `𝓜𝒮𝒫^u` and
`𝓜𝒮𝒫^l` are equivalent to the linear programs (4.2) and (4.6), respectively: their optimal values
coincide. The hypothesis on the second equality (`2 ≤ k`, or some row of `Ŵ` below (2.1b) is nonzero)
is not in the paper: for `k = 1` (so `Ξ = {1}`) and `W` with zero rows below (2.1b), the cone `𝒦` of
Proposition 3 is all of `ℝ` while `𝒦_ℙ = [0, ∞)`, and the second equality fails (e.g. `T = 1`, `A = 1`,
`B = 0`, `C = -1`: `𝓜𝒮𝒫^l` has value `0`, (4.6) is unbounded below). The hypothesis excludes exactly
that case. The first equality is stated without it, as printed. -/
theorem theorem_3 (σ : Setting) (hσ : σ.Standing) (hM : σ.LinearCondMean)
    (hsf : σ.StrictlyFeasible) :
    σ.valMSPu = σ.valLP42 ∧
      ((2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) → σ.valMSPl = σ.valLP46) := by sorry

end PrimalDualLDR.Multistage
