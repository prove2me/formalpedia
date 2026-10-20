-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_exponential_jointConvex
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.exponential_jointConvex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:12:26.157534+00:00
-- url     : https://prove2.me/theorems/0ee627fc-31fb-4590-9580-867be8ead31e
-- title:
--   Lemma 18: joint convexity of the exponential functional
-- statement:
--   For $\alpha\in[1,2]$, let $Q_\alpha(\rho,\sigma)$ denote $2^{(\alpha-1)\widetilde D_\alpha(\rho\|\sigma)}$ for $\alpha>1$, retaining positive infinity on support failure, and set $Q_1(\rho,\sigma)=\operatorname{Tr}\rho=1$ on density pairs. For normalized $\rho_1,\rho_2,\sigma_1,\sigma_2\ge0$ and $\lambda\in[0,1]$,
--
--   $$
--   Q_\alpha(\lambda\rho_1+(1-\lambda)\rho_2,\lambda\sigma_1+(1-\lambda)\sigma_2)\le\lambda Q_\alpha(\rho_1,\sigma_1)+(1-\lambda)Q_\alpha(\rho_2,\sigma_2).
--   $$
--
--   The endpoint is the raw trace-functional extension, without evaluating $0\cdot(+\infty)$. The normalized domain follows footnote 46; no continuity in order at support-mismatched pairs is claimed.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 22, Lemma 18

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.22, Lemma 18, and p.26 footnote 46: normalized joint convexity.
At alpha=1 the expression means the raw trace extension, identically one here,
not the indeterminate extended product 0 times D. -/
theorem exponential_jointConvex {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) : NormalizedJointConvex (exponential (I := I) a) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
