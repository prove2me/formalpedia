-- Prove2me | Theorems.Thm_TierneyMH1998_maxMHKernel_offDiag_maximal_faithful
-- name    : TierneyMH1998.maxMHKernel_offDiag_maximal_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:59:51.412832+00:00
-- url     : https://prove2.me/theorems/d97e6016-7618-4212-8140-19c626ef0284
-- title:
--   Section 3, p. 7: the maximal Metropolis–Hastings kernel dominates every reversible Metropolis–Hastings kernel with the same proposal off the diagonal
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space with measurable singletons, $\pi$ a probability measure on $E$, $Q$ a Markov proposal kernel and $\alpha : E\times E \to [0,1]$ measurable such that the Metropolis–Hastings kernel $P_\alpha(x,dy) = Q(x,dy)\alpha(x,y) + \delta_x(dy)\int(1-\alpha(x,u))Q(x,du)$ satisfies detailed balance with respect to $\pi$. Then the maximal Metropolis–Hastings kernel $P_{MH}$ for $Q$ (acceptance $\alpha_{MH}$) dominates $P_\alpha$ off the diagonal: for $\pi$-almost every $x$ and all $A \in \mathcal E$,
--
--   $$P_{MH}(x, A\setminus\{x\}) \;\ge\; P_\alpha(x, A\setminus\{x\}).$$
--
--   This is the maximality of the Metropolis–Hastings acceptance probability among reversible Metropolis–Hastings kernels with a common proposal, which Tierney (1998, Section 3, p. 7) attributes to Peskun; combined with Theorem 4 it shows that $\alpha_{MH}$ minimizes asymptotic variance for a given proposal.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, doi:10.1214/aoap/1027961031, p. 7, Section 3

import Mathlib
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Definitions.Def_TierneyMH_Shared_mhKernel
import Definitions.Def_TierneyMH_Mixture_maxMHKernel

open TierneyMH.Shared TierneyMH.Mixture

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem TierneyMH1998.maxMHKernel_offDiag_maximal_faithful {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q]
    (α : E × E → ℝ≥0∞) (hα_meas : Measurable α) (hα_le : ∀ p, α p ≤ 1)
    (hrev : Kernel.IsReversible (mhKernel Q α) π) :
    OffDiagDominates π (maxMHKernel π Q) (mhKernel Q α) := by sorry
