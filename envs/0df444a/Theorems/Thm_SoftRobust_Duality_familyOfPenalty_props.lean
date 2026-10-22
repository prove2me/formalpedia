-- Prove2me | Theorems.Thm_SoftRobust_Duality_familyOfPenalty_props
-- name    : SoftRobust.Duality.familyOfPenalty_props
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T18:49:25.579235+00:00
-- url     : https://prove2.me/theorems/9139c765-bccb-4ccb-b1b1-fecafedd90b2
-- title:
--   Proof of Theorem 2.1, converse: $\mathbf Q^\alpha$ is nondecreasing and convex, and $\mathcal Q^\alpha(0)\neq\emptyset$
-- statement:
--   Let $\alpha:\mathcal P\to[0,\infty]$ be a penalty on the probability measures of $(\Omega,\mathcal F)$ that is convex in the sense of mixtures and normalized ($\alpha(\mathbb Q) = 0$ for some $\mathbb Q$). Define
--
--   $$
--   \mathcal Q^\alpha(\varepsilon) = \{\mathbb Q\in\mathcal P : \alpha(\mathbb Q)\le\varepsilon\}, \qquad \varepsilon\ge0 .
--   $$
--
--   Then the family $\mathbf Q^\alpha = \{\mathcal Q^\alpha(\varepsilon) : \varepsilon\ge0\}$ is nondecreasing and convex (if $\mathbb Q_i\in\mathcal Q^\alpha(\varepsilon_i)$, then $\lambda\mathbb Q_1+(1-\lambda)\mathbb Q_2\in\mathcal Q^\alpha(\lambda\varepsilon_1+(1-\lambda)\varepsilon_2)$ for $\lambda\in[0,1]$), and $\mathcal Q^\alpha(0)$ is nonempty.
--
--   This is the first step of the converse half of Theorem 2.1: every normalized convex penalty produces a family to which the forward half applies.
-- source:
--   Ben-Tal, Bertsimas, Brown, A Soft Robust Model for Optimization Under Ambiguity, Oper. Res. 58(4) (2010), p. 1224, §2.3, proof of Theorem 2.1, converse

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace SoftRobust.Duality

/-- §2.3, proof of Theorem 2.1, p. 1224 (converse, first step): for a convex, normalized penalty
`α`, the family `𝐐^α = {𝒬^α(ε) : ε ≥ 0}`, `𝒬^α(ε) = {ℚ : α(ℚ) ≤ ε}`, is nondecreasing and convex, and
`𝒬^α(0)` is nonempty. -/
theorem familyOfPenalty_props {Ω : Type*} [MeasurableSpace Ω]
    (α : ProbabilityMeasure Ω → ℝ≥0∞) (hconv : IsConvexPenalty α)
    (hnorm : IsNormalizedPenalty α) :
    IsAdmissibleFamily (familyOfPenalty α) := by sorry

end SoftRobust.Duality
