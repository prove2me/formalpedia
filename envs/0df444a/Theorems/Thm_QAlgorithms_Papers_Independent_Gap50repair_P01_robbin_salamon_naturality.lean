-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_robbin_salamon_naturality
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.robbin_salamon_naturality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:25:21.003974+00:00
-- url     : https://prove2.me/theorems/b5c7023a-95ff-45a5-9d5b-379988aa126a
-- title:
--   Proposition 48
-- statement:
--   For arbitrary continuous symplectic paths $\psi,\phi:[0,1]\to\operatorname{Sp}(2n,\mathbb R)$ define $\psi'(t)=\phi(t)\psi(t)\phi(t)^{-1}$. Then the graph Robbin–Salamon index satisfies
--
--   $$\mu_{\rm RS}(\psi')=\mu_{\rm RS}(\psi).$$
--
--   The conjugating path may depend on time. No start-at-identity condition or final nondegeneracy is assumed. This is the naturality statement for the generalized graph index.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 48, Proposition 48

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 48, PDF p.48: time-dependent conjugacy of arbitrary paths. -/
theorem robbin_salamon_naturality {n : ℕ} (p phi : ℝ → GroupedRealMatrix n)
    (hp : IsPath p 1) (hphi : IsPath phi 1) :
    robbinSalamon (fun t => phi t*p t*(phi t)⁻¹) = robbinSalamon p := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
