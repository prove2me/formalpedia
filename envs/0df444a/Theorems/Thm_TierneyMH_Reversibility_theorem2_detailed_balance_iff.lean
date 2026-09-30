-- Prove2me | Theorems.Thm_TierneyMH_Reversibility_theorem2_detailed_balance_iff
-- name    : TierneyMH.Reversibility.theorem2_detailed_balance_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T12:00:05.981818+00:00
-- url     : https://prove2.me/theorems/d644627b-84e3-4754-a268-bc0a04e631fa
-- title:
--   Theorem 2: a Metropolis–Hastings kernel satisfies detailed balance iff $\alpha=0$ a.e. off $R$ and $\alpha(x,y)r(x,y)=\alpha(y,x)$ a.e. on $R$
-- statement:
--   Let $\pi$ be a probability measure on a measurable space $(E,\mathcal E)$, let $Q$ be a Markov transition kernel on $E$ (the proposal), and let $\alpha:E\times E\to[0,1]$ be measurable (the acceptance probability). Let $P$ be the Metropolis–Hastings kernel
--   $P(x,dy)=Q(x,dy)\alpha(x,y)+\delta_x(dy)\int(1-\alpha(x,u))Q(x,du)$,
--   and put $\mu(dx,dy)=\pi(dx)Q(x,dy)$ and $\mu^T(dx,dy)=\mu(dy,dx)$. Let $R$ be any symmetric set on which $\mu$ and $\mu^T$ are mutually absolutely continuous and off which they are mutually singular, and let $r$ be any version of $d\mu_R/d\mu^T_R$ with $0<r<\infty$ and $r(x,y)=1/r(y,x)$ everywhere (Proposition 1). Then $P$ satisfies detailed balance, $\pi(dx)P(x,dy)=\pi(dy)P(y,dx)$, if and only if
--
--   1. $\alpha$ is $\mu$-almost everywhere zero on $R^c$, and
--   2. $\alpha$ satisfies
--
--   $$\alpha(x,y)\,r(x,y)=\alpha(y,x)\qquad\mu\text{-almost everywhere on }R.$$
--
--   This gives necessary and sufficient conditions on the proposal kernel and the acceptance probability for a Metropolis–Hastings sampler to be reversible with respect to $\pi$ on a general state space, with no density or dominating measure assumed. The standard Metropolis–Hastings acceptance probability and many special cases of the literature (common dominating measure, deterministic proposals, dimension-changing moves) are instances.
--
--   **Formalization Note** The paper states the theorem for "the detailed balance condition (4)", $\mu(dx,dy)\alpha(x,y)=\mu^T(dx,dy)\alpha(y,x)$, which the text on pp. 2–3 identifies with detailed balance (2) of the kernel; the statement here uses (2) for the kernel itself, as Mathlib's `Kernel.IsReversible (mhKernel Q α) π`. The pair $(R,r)$ is universally quantified, so the theorem holds for every version. $\mu=\pi\otimes Q$ is `π ⊗ₘ Q`, $\mu^T$ is its image under the swap, and "$\mu$-a.e. on $R$" is almost everywhere for the restriction of $\mu$ to $R$. $\alpha$ and $r$ are `ℝ≥0∞`-valued.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 3, Theorem 2

import Mathlib
import Definitions.Def_TierneyMH_Shared_mhKernel
import Definitions.Def_TierneyMH_Shared_IsSymmetricSplit
import Definitions.Def_TierneyMH_Shared_IsRatioVersion

open TierneyMH.Shared

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Reversibility

/-- **Theorem 2** (Tierney 1998, p. 3). Let `π` be a probability measure and `Q` a Markov kernel
on a measurable space `E`, let `α : E × E → [0, 1]` be measurable, and put
`μ(dx, dy) = π(dx) Q(x, dy)` (`μ = π ⊗ₘ Q`). Let `(R, r)` be **any** pair given by
Proposition 1 for `μ`. Then the Metropolis–Hastings kernel `mhKernel Q α` of Eq. (1) satisfies
detailed balance with respect to `π` if and only if
* (i) `α = 0` `μ`-almost everywhere on `Rᶜ`, and
* (ii) `α(x, y) r(x, y) = α(y, x)` `μ`-almost everywhere on `R`.

The paper names detailed balance in the form (4) `μ(dx, dy) α(x, y) = μᵀ(dx, dy) α(y, x)`,
which the text on pp. 2–3 identifies with (2) for the kernel (1); the statement here uses (2)
itself, `Kernel.IsReversible (mhKernel Q α) π`. -/
theorem theorem2_detailed_balance_iff {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q]
    (α : E × E → ℝ≥0∞) (hα_meas : Measurable α) (hα_le : ∀ p, α p ≤ 1)
    (R : Set (E × E)) (r : E × E → ℝ≥0∞)
    (hR : IsSymmetricSplit (π ⊗ₘ Q) R) (hr : IsRatioVersion (π ⊗ₘ Q) R r) :
    Kernel.IsReversible (mhKernel Q α) π ↔
      ((∀ᵐ p ∂((π ⊗ₘ Q).restrict Rᶜ), α p = 0) ∧
        (∀ᵐ p ∂((π ⊗ₘ Q).restrict R), α p * r p = α p.swap)) := by sorry

end TierneyMH.Reversibility
