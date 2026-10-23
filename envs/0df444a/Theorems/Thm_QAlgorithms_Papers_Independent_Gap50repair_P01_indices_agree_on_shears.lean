-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_indices_agree_on_shears
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.indices_agree_on_shears
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:29:23.511975+00:00
-- url     : https://prove2.me/theorems/4bc70dc3-9ff3-4a1d-ad54-bfa66c1bc0a9
-- title:
--   Proposition 60
-- statement:
--   Let $B:[0,1]\to\operatorname{Mat}(n,\mathbb R)$ be continuous and symmetric at every time. For the upper symplectic shear $\psi(t)=\left(\begin{smallmatrix}I&B(t)\\0&I\end{smallmatrix}\right)$,
--
--   $$\mu_{\rm RS}(\psi)=\mu_{\rm RS2}(\psi).$$
--
--   The first index uses the symplectic graph and diagonal; the second uses the image of the fixed vertical Lagrangian. The assertion is limited to the upper shears of Definition 53 and does not silently include arbitrary conjugates or lower shears. This records the common case of the two otherwise different indices.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 59, Proposition 60

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 60, PDF p.59: equality on the upper shears of Definition 53. -/
theorem indices_agree_on_shears {n : ℕ} (B : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hc : ContinuousOn B (Set.Icc (0 : ℝ) 1))
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, (B t).transpose = B t) :
    robbinSalamon (fun t => shear (B t)) = robbinSalamonVertical (fun t => shear (B t)) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
