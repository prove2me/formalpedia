-- Prove2me | Theorems.Thm_TierneyMH_Reversibility_mhKernel_reversible_iff_offDiagonal
-- name    : TierneyMH.Reversibility.mhKernel_reversible_iff_offDiagonal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T11:51:28.610172+00:00
-- url     : https://prove2.me/theorems/02172cae-4ba9-4eaf-86e0-70195dde848e
-- title:
--   Eqs. (2)–(3): the Metropolis–Hastings kernel satisfies detailed balance iff its off-diagonal part does
-- statement:
--   Let $\pi$ be a probability measure on a measurable space $(E,\mathcal E)$, let $Q$ be a Markov transition kernel on $E$, let $\alpha:E\times E\to[0,1]$ be measurable, and let $P$ be the Metropolis–Hastings kernel
--   $P(x,dy)=Q(x,dy)\alpha(x,y)+\delta_x(dy)\int(1-\alpha(x,u))Q(x,du)$.
--   Then $P$ satisfies the detailed balance relation
--
--   $$\pi(dx)P(x,dy)=\pi(dy)P(y,dx)\tag{2}$$
--
--   if and only if
--
--   $$\pi(dx)Q(x,dy)\alpha(x,y)=\pi(dy)Q(y,dx)\alpha(y,x),\tag{3}$$
--
--   both sides being measures on $\mathcal E\otimes\mathcal E$. That is, the diagonal (rejection) component of $P$ does not matter.
--
--   This reduces reversibility of the Metropolis–Hastings kernel to an identity between two measures built from $\pi$, $Q$ and $\alpha$ alone, which is the starting point of Theorem 2.
--
--   **Formalization Note** Detailed balance (2) is Mathlib's `Kernel.IsReversible P π`: $\int_A P(x,B)\,\pi(dx)=\int_B P(x,A)\,\pi(dx)$ for all measurable $A,B$, which is (2) evaluated on measurable rectangles. The measure $\pi(dx)Q(x,dy)\alpha(x,y)$ is `(π ⊗ₘ Q).withDensity α`, and the right side of (3) is its image under the swap $(x,y)\mapsto(y,x)$. $\alpha$ is `ℝ≥0∞`-valued with $\alpha\le1$.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 2, §2, Eqs. (2)–(3)

import Mathlib
import Definitions.Def_TierneyMH_Shared_mhKernel

open TierneyMH.Shared

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Reversibility

/-- **§2, Eqs. (2)–(3)** (Tierney 1998, p. 2). The Metropolis–Hastings kernel `P = mhKernel Q α`
of Eq. (1) satisfies detailed balance (2) `π(dx) P(x, dy) = π(dy) P(y, dx)` if and only if
(3) `π(dx) Q(x, dy) α(x, y) = π(dy) Q(y, dx) α(y, x)` holds as an identity of measures on
`E × E`: the diagonal (rejection) component does not matter.

Detailed balance (2) is Mathlib's `Kernel.IsReversible P π`
(`∫_A P(x, B) π(dx) = ∫_B P(x, A) π(dx)` for measurable `A, B`). The measure
`π(dx) Q(x, dy) α(x, y)` is `(π ⊗ₘ Q).withDensity α`, and `π(dy) Q(y, dx) α(y, x)` is its image
under `Prod.swap`. -/
theorem mhKernel_reversible_iff_offDiagonal {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q]
    (α : E × E → ℝ≥0∞) (hα_meas : Measurable α) (hα_le : ∀ p, α p ≤ 1) :
    Kernel.IsReversible (mhKernel Q α) π ↔
      ((π ⊗ₘ Q).withDensity α).map Prod.swap = (π ⊗ₘ Q).withDensity α := by sorry

end TierneyMH.Reversibility
