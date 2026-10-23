-- Prove2me | Theorems.Thm_TierneyMH1998_proposition5_mixture_faithful
-- name    : TierneyMH1998.proposition5_mixture_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T00:59:49.587433+00:00
-- url     : https://prove2.me/theorems/a479d39e-1991-4970-9511-f3eed643c4f2
-- title:
--   Proposition 5 (mixture proposals), as stated: no countable generation of the $\sigma$-algebra
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space with measurable singletons, $\pi$ a probability measure on $E$, $(Q_i)_{i \in I}$ a countable family of Markov proposal kernels on $E$ and $\beta_i \ge 0$ with $\sum_i \beta_i = 1$. For a proposal kernel $K$, write $P_K$ for its maximal Metropolis–Hastings kernel, $P_K(x,dy) = K(x,dy)\alpha^K_{MH}(x,y) + \delta_x(dy)\int (1-\alpha^K_{MH}(x,u))K(x,du)$, where $\alpha^K_{MH}(x,y) = \min\{1, r(y,x)\}$ on the set $R$ where $\pi(dx)K(x,dy)$ and its transpose are mutually absolutely continuous and $0$ off $R$. Let $Q = \sum_i \beta_i Q_i$. Then for $\pi$-almost every $x$,
--
--   $$P_Q(x, A\setminus\{x\}) \;\ge\; \sum_i \beta_i\, P_{Q_i}(x, A\setminus\{x\}) \qquad \text{for every } A \in \mathcal E.$$
--
--   This is Proposition 5 of Tierney (1998) as stated, on an arbitrary measurable space: the maximal kernel of a mixture proposal dominates the mixture of the maximal kernels off the diagonal. The existing theorem TierneyMH.Mixture.proposition5_mixture proves it under the additional assumption that $\mathcal E$ is countably generated.
--
--   **Formalization Note** Measurable singletons are the paper's implicit requirement that $A\setminus\{x\}$ be an event. Weights are in $\mathbb R_{\ge 0}$ with $\sum_i \beta_i = 1$ as a `HasSum`; a sequence of kernels is a countable index type.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, doi:10.1214/aoap/1027961031, p. 7, Proposition 5 (proof p. 8)

import Mathlib
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Definitions.Def_TierneyMH_Mixture_maxMHKernel
import Definitions.Def_TierneyMH_Mixture_mixKernel

open TierneyMH.Shared TierneyMH.Mixture

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem TierneyMH1998.proposition5_mixture_faithful {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π]
    {ι : Type*} [Countable ι] (Q : ι → Kernel E E) [∀ i, IsMarkovKernel (Q i)]
    (β : ι → ℝ≥0) (hβ : HasSum β 1) :
    OffDiagDominates π (maxMHKernel π (mixKernel β Q))
      (mixKernel β fun i => maxMHKernel π (Q i)) := by sorry
