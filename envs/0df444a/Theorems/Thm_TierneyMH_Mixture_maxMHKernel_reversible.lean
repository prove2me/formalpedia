-- Prove2me | Theorems.Thm_TierneyMH_Mixture_maxMHKernel_reversible
-- name    : TierneyMH.Mixture.maxMHKernel_reversible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T03:02:13.289271+00:00
-- url     : https://prove2.me/theorems/ef76a00c-24a9-47c9-a6a0-4875b1908306
-- title:
--   The maximal Metropolis–Hastings kernel satisfies detailed balance
-- statement:
--   Let $\pi$ be a probability measure and $Q$ a Markov proposal kernel on a measurable space $(E,\mathcal E)$. The maximal Metropolis–Hastings kernel $P$ for $Q$, the kernel (1) with acceptance probability $\alpha_{MH}$, satisfies the detailed balance relation
--
--   $$\pi(dx)\,P(x,dy)=\pi(dy)\,P(y,dx)$$
--
--   as measures on $\mathcal E\otimes\mathcal E$. In particular $\pi$ is invariant for $P$.
--
--   In the paper this follows from the fact that $\alpha_{MH}$ satisfies conditions (i) and (ii) together with Theorem 2. It is what makes the off-diagonal ordering of Proposition 5 a comparison between kernels with invariant distribution $\pi$, as the definition of $\succeq$ presupposes.
--
--   **Formalization Note** Detailed balance is Mathlib's `Kernel.IsReversible`: $\int_A P(x,B)\,\pi(dx)=\int_B P(x,A)\,\pi(dx)$ for all measurable $A,B$.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 3, §2 (α_MH satisfies (i)–(ii); by Theorem 2 the maximal kernel is reversible)

import Mathlib
import Definitions.Def_TierneyMH_Mixture_maxMHKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Mixture

/-- **The maximal Metropolis–Hastings kernel is reversible** (Tierney 1998, §2, p. 3:
`α_MH` satisfies (i)–(ii), so by Theorem 2 the kernel satisfies detailed balance).
For a probability measure `π` and a Markov proposal kernel `Q`, the kernel (1) with
acceptance probability `α_MH` satisfies the detailed balance relation (2),
`π(dx) P(x, dy) = π(dy) P(y, dx)`. -/
theorem maxMHKernel_reversible {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q] :
    Kernel.IsReversible (maxMHKernel π Q) π := by sorry

end TierneyMH.Mixture
