-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_reductionToTableaux
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.reductionToTableaux
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:37:59.224175+00:00
-- url     : https://prove2.me/theorems/05eccfdc-2d21-4f58-84b3-876ea34fa620
-- title:
--   Optimization reduces to definite tableaux
-- statement:
--   Let $\nu$ have $N\ge2$ boxes, let $d\ge c_1$, and let $W_\nu$ be its full isotypic subspace. Let $\lambda_1(\psi)$ be the largest Schmidt amplitude for the last-particle cut. For each standard tableau $t$ of shape $\nu$, let $P_t$ be the Hermitian Young projector. Then
--
--   $$
--   \sup_{\psi\in W_\nu,\ \|\psi\|=1}\lambda_1(\psi)^2
--   =\max_{t\in\operatorname{Std}(\nu)}
--   \sup_{\psi\in\operatorname{Im}P_t,\ \|\psi\|=1}\lambda_1(\psi)^2.
--   $$
--
--   Thus the optimization reduces to individual tableau spaces. The maximum over tableaux remains outside each unit-sphere supremum.
--
--   **Formalization Note** The physical space $\operatorname{Im}P_t$ is exactly $V^\nu\otimes|t\rangle$; using it avoids arbitrary representation coordinates.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 14, Lemma 10, equation (44)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Lemma 10, arXiv:1805.00364v2 PDF p.14, equation (44).
The maximum over tableaux is outside their individual unit-sphere suprema. -/
theorem reductionToTableaux {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n) :
    IsGreatest {r : ℝ | ∃ t : Filling n, IsTableau nu.val t ∧
      r = subspaceOptimum (tableauSpace d t)}
      (subspaceOptimum (isotypicSpace nu)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
