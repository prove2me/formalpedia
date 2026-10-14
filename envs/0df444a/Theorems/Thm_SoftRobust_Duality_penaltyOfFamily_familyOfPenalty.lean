-- Prove2me | Theorems.Thm_SoftRobust_Duality_penaltyOfFamily_familyOfPenalty
-- name    : SoftRobust.Duality.penaltyOfFamily_familyOfPenalty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:49:22.419209+00:00
-- url     : https://prove2.me/theorems/29dccffa-d179-4c91-a579-30941d655166
-- title:
--   Proof of Theorem 2.1, converse: $\alpha^{Q^\alpha} = \alpha$
-- statement:
--   Let $\alpha:\mathcal P\to[0,\infty]$ be any penalty on the probability measures of $(\Omega,\mathcal F)$, and let $\mathcal Q^\alpha(\varepsilon) = \{\mathbb Q : \alpha(\mathbb Q)\le\varepsilon\}$. Then the penalty of the family $\mathbf Q^\alpha$ is $\alpha$ itself: for every $\mathbb Q \in \mathcal P$,
--
--   $$
--   \alpha^{Q^\alpha}(\mathbb Q) = \inf\{\varepsilon\ge0 : \mathbb Q\in\mathcal Q^\alpha(\varepsilon)\} = \alpha(\mathbb Q).
--   $$
--
--   Together with the forward half of Theorem 2.1 applied to $\mathbf Q^\alpha$, this gives the converse half.
--
--   **Formalization Note** With $\alpha$ valued in $[0,\infty]$ the identity holds for every $\alpha$, including at measures with $\alpha(\mathbb Q)=\infty$ (both sides are $\infty$, the left one as an empty infimum).
-- source:
--   Ben-Tal, Bertsimas, Brown, A Soft Robust Model for Optimization Under Ambiguity, Oper. Res. 58(4) (2010), p. 1224, §2.3, proof of Theorem 2.1, converse (α^{Q^α} = α)

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace SoftRobust.Duality

/-- §2.3, proof of Theorem 2.1, p. 1224 (converse, second step): `α^{Q^α} = α`, i.e.
`inf{ε ≥ 0 : ℚ ∈ 𝒬^α(ε)} = α(ℚ)` for every probability measure `ℚ`. -/
theorem penaltyOfFamily_familyOfPenalty {Ω : Type*} [MeasurableSpace Ω]
    (α : ProbabilityMeasure Ω → ℝ≥0∞) :
    penaltyOfFamily (familyOfPenalty α) = α := by sorry

end SoftRobust.Duality
