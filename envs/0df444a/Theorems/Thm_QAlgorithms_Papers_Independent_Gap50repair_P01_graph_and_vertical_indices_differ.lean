-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_graph_and_vertical_indices_differ
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.graph_and_vertical_indices_differ
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:28:40.763245+00:00
-- url     : https://prove2.me/theorems/3cde40dc-128b-4be5-a2bb-5b35281f939f
-- title:
--   Proposition 58
-- statement:
--   Let $\mu_{\rm RS}$ be the index of $\operatorname{Gr}\psi$ relative to the diagonal in the doubled space with form $-\Omega_0\oplus\Omega_0$. Let $V=\{0\}\times\mathbb R^n$ and let $\mu_{\rm RS2}$ be the Lagrangian index of $\psi V$ relative to $V$. Then
--
--   $$\exists n\ge1\ \exists\text{ continuous }\psi:[0,1]\to\operatorname{Sp}(2n,\mathbb R),\quad \mu_{\rm RS}(\psi)\ne\mu_{\rm RS2}(\psi).$$
--
--   The claim is existential, not that the indices differ on every path. This distinguishes the graph and fixed-vertical constructions.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 58, Proposition 58

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 58, PDF p.58: existence of disagreement, not universal disagreement. -/
theorem graph_and_vertical_indices_differ :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ p : ℝ → GroupedRealMatrix n,
      IsPath p 1 ∧ robbinSalamon p ≠ robbinSalamonVertical p := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
