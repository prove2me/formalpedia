-- Prove2me | Theorems.Thm_RiskSensMDP_Discounted_cost_iteration
-- name    : RiskSensMDP.Discounted.cost_iteration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:35.624631+00:00
-- url     : https://prove2.me/theorems/f689a4c1-1ddb-48ff-a0fa-27252e466428
-- title:
--   Theorem 3.6(a) — cost iteration for a discounted Markov policy
-- statement:
--   Let $\pi=(f_0,f_1,\ldots)$ be a sequence of admissible measurable decision rules on $\hat E$, in the bounded positive-cost model under (CC). For $1\le n\le N$ and $(x,y,z)\in\hat E$, the expected utility under $\pi$ is obtained by composing its first $n$ one-step operators:
--
--   $$V_{n\pi}(x,y,z)=\bigl(T_{f_0}T_{f_1}\cdots T_{f_{n-1}}U\bigr)(x,y,z),\qquad U(x,y,z)=U(y).$$
--
--   This identifies the cost iteration of a fixed Markov policy before minimizing over policies. **Formalization Note** The evaluation of $\pi$ uses the history-policy embedding shifted by the initial $(y,z)$; its $(0,1)$ instance is the embedding displayed in the paper.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 11, Theorem 3.6(a)

import Mathlib
import Definitions.Def_RiskSensMDP_Discounted_Model

open MeasureTheory ProbabilityTheory Filter

namespace RiskSensMDP.Discounted

/-- Theorem 3.6(a), authors' manuscript p. 11: cost iteration for an extended-state
Markov policy. Formalization Note: `markovValue` uses the `(y,z)`-shifted embedding
of the Markov rules into finite-dimensional path expectations. -/
theorem cost_iteration {E A : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [StandardBorelSpace A]
    (M : Model E A) (hBounds : HasBounds M) (hCC : HasCC M)
    (N : ℕ) (π : MarkovPolicy M) :
    ∀ n ∈ Finset.Icc 1 N, ∀ s ∈ extendedDomain E,
      markovValue M π n s.1 s.2.1 s.2.2 = policyIteration M π n s := by sorry

end RiskSensMDP.Discounted
