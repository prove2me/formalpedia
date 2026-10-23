-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_classical_index_characterization
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.classical_index_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:22:49.115374+00:00
-- url     : https://prove2.me/theorems/cd3d489a-55df-48d0-b0dd-80a49b0d8e78
-- title:
--   Proposition 37
-- statement:
--   Fix $n\ge1$. On continuous admissible paths $\gamma:[0,1]\to\operatorname{Sp}(2n,\mathbb R)$, the classical index satisfies and is uniquely determined by three properties: invariance under homotopies through admissible paths; the loop rule for a based symplectic loop $\phi$; and the signature normalization for symmetric nondegenerate $S$ whose eigenvalues have absolute value below $2\pi$:
--
--   $$\mu_{\rm CZ}(\phi\gamma)=\mu_{\rm CZ}(\gamma)+2\deg(\rho\circ\phi),\qquad \mu_{\rm CZ}(e^{tJ_0S})=\tfrac12\operatorname{Sign}S.$$
--
--   Every integer-valued assignment with these properties equals the constructed index on every admissible path. Endpoints may move within $\operatorname{Sp}^*$ during an admissible homotopy. This is a uniqueness theorem as well as a list of properties.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 40, Proposition 37

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 37, PDF pp.40–41: properties and uniqueness on the entire admissible domain. -/
theorem classical_index_characterization {n : ℕ} (hn : 1 ≤ n) :
    CzThreeAxioms (n := n) (fun p : ℝ → GroupedRealMatrix n => conleyZehnder p 1) ∧
    (∀ f : (ℝ → GroupedRealMatrix n) → ℤ, CzThreeAxioms f →
      ∀ p : ℝ → GroupedRealMatrix n, IsAdmissible p 1 → f p = conleyZehnder p 1) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
