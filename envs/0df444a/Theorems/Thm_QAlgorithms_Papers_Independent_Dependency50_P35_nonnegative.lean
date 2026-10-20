-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_nonnegative
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.nonnegative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:52:31.285268+00:00
-- url     : https://prove2.me/theorems/ace35844-34b6-4fba-8a67-32222f4f7f8e
-- title:
--   Theorem 3: nonnegativity under trace ordering
-- statement:
--   Let $\alpha>0$, $\alpha\ne1$, and let $\rho,\sigma\ge0$ be finite-dimensional complex operators with $\rho\ne0$ and $\operatorname{Tr}\rho\ge\operatorname{Tr}\sigma$. For the trace-normalized sandwiched divergence of Definition 2, in bits,
--
--   $$
--   \widetilde D_\alpha(\rho\|\sigma)\ge0,
--   \qquad \rho=\sigma\ \Longrightarrow\ \widetilde D_\alpha(\rho\|\sigma)=0.
--   $$
--
--   The inequalities include positive-infinite divergences and require neither trace-one normalization nor support domination. This is the source's two-clause positivity result.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 8, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.8, Theorem 3: both nonnegativity and the equality-on-the-diagonal clause,
for every positive order other than one and arbitrary traces. -/
theorem nonnegative {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a ∧ a ≠ 1) (rho sigma : Mat I)
    (hr : rho.PosSemidef) (hs : sigma.PosSemidef) (hn : rho ≠ 0)
    (ht : tr sigma ≤ tr rho) :
    0 ≤ divergence a rho sigma ∧ (rho = sigma → divergence a rho sigma = 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
