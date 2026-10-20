-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_sharpLastParticle
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.sharpLastParticle
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:33:22.267952+00:00
-- url     : https://prove2.me/theorems/50fd4a84-98eb-4740-a0b6-f3da4cf003c3
-- title:
--   Sharp largest last-particle Schmidt coefficient
-- statement:
--   Let $\nu$ be a Young diagram with $N\ge2$ boxes and column lengths $c_1,\ldots,c_{r_1}$, and let $d\ge c_1$. Let $W_\nu\subset(\mathbb C^d)^{\otimes N}$ be its entire Schur–Weyl isotypic component. For a vector $\psi$, write $\lambda_1(\psi)$ for its largest Schmidt amplitude across the first $N-1$ physical factors versus the final factor. If $h_{(i,l)}$ is the hook length in the original diagram and $\mathcal R(\nu)$ is the set of removable boxes, then
--
--   $$
--   \sup_{\psi\in W_\nu,\ \|\psi\|=1}\lambda_1(\psi)^2
--   =\max_{(c_l,l)\in\mathcal R(\nu)}\prod_{i=1}^{c_l-1}\left(1-\frac1{h_{(i,l)}}\right).
--   $$
--
--   This gives the sharp upper bound on the largest eigenvalue of the physical one-particle marginal.
--
--   **Formalization Note** The Lean conclusion uses the greatest element of the finite set of corner products to express the maximum. The largest squared Schmidt amplitude is the operator norm of the explicitly computed positive last marginal.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 5, Theorem 1, equation (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Theorem 1, arXiv:1805.00364v2 PDF p.5, equation (13).
IsGreatest states equality of the unit-sphere supremum to the actual maximum
of the removable-corner products, rather than an unguarded empty-set supremum. -/
theorem sharpLastParticle {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n) :
    IsGreatest {r : ℝ | ∃ b, Removable nu.val b ∧ r = cornerBound nu.val b}
      (subspaceOptimum (isotypicSpace nu)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
