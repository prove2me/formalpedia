-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_alternative_rotation_degree
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.alternative_rotation_degree
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:23:22.736399+00:00
-- url     : https://prove2.me/theorems/130433e8-5fe4-459d-b4e4-f56fc34bc308
-- title:
--   Proposition 38
-- statement:
--   Let $n\ge1$, let $\gamma$ be admissible on $[0,1]$, and let $e$ be any admissible extension of Definition 33. Let $r:\operatorname{Sp}(2n,\mathbb R)\to S^1$ be continuous and agree with $\det_\mathbb C$ on $U(n)$. Require $r(W^-)\in\{1,-1\}$ and $\deg(r^2\circ\psi_2^-)=n-1$, where $\psi_2^-(t)=e^{t\pi J_0S^-}$ and $S^-$ is the explicit matrix on p.41. Then
--
--   $$\mu_{\rm CZ}(\gamma)=\deg(r^2\circ e).$$
--
--   The reference matrix has first symplectic-plane off-diagonal entries $-\log 2/\pi$ and identity on the other planes. It is constructed from $n$, not chosen to make the degree condition hold. This gives the precise permissible replacements for the rotation map.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 41, Proposition 38

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 38, PDF pp.41–42: both W^- and the reference degree are required. -/
theorem alternative_rotation_degree {n : ℕ} (hn : 1 ≤ n)
    (p e : ℝ → GroupedRealMatrix n) (hp : IsAdmissible p 1) (he : IsExtension p e)
    (r : GroupedRealMatrix n → ℂ) (hc : ContinuousOn r {A | IsSymplectic A})
    (hcircle : ∀ A, IsSymplectic A → ‖r A‖ = 1)
    (hdet : ∀ A, IsUnitaryReal A → r A = complexActionDet A)
    (hw : r (wMinus n) = 1 ∨ r (wMinus n) = -1)
    (href : winding (fun t => r (referenceMinus n t)^2) 1 = (n : ℤ)-1) :
    conleyZehnder p 1 = winding (fun t => r (e t)^2) 2 := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
