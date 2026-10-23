-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_regular_crossing_formula
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.regular_crossing_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:25:56.177911+00:00
-- url     : https://prove2.me/theorems/d97d65c2-834a-4dfe-b204-a7fc77a4445f
-- title:
--   Proposition 51
-- statement:
--   Let $\psi:[0,1]\to\operatorname{Sp}(2n,\mathbb R)$ be smooth. Put $S_t=-J_0\dot\psi_t\psi_t^{-1}$ and let $\Gamma(\psi,t)$ be $v^\mathsf TS_tw$ restricted to $\ker(\psi_t-I)$. Assume all crossings are regular, meaning these restricted bilinear forms are nondegenerate. The interior crossing set is finite, and
--
--   $$\mu_{\rm RS}(\psi)=\tfrac12\operatorname{Sign}\Gamma(\psi,0)+\sum_{0<t<1\atop t\ \rm crossing}\operatorname{Sign}\Gamma(\psi,t)+\tfrac12\operatorname{Sign}\Gamma(\psi,1).$$
--
--   A noncrossing endpoint has signature zero on the zero space. Endpoint derivatives are taken within the interval. Finiteness is concluded rather than added as a hypothesis. This is the graph crossing formula.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 49, Proposition 51

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 51, PDF p.49: finiteness is established, not assumed. -/
theorem regular_crossing_formula {n : ℕ} (p : ℝ → GroupedRealMatrix n) (hp : IsRegular false p) :
    (crossings false p).Finite ∧ robbinSalamon p =
      (crossingSignature false p 0 : ℚ)/2 + (interiorCrossingSum false p : ℚ) +
      (crossingSignature false p 1 : ℚ)/2 := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
