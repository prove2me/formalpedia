-- Prove2me | Theorems.Thm_VaryingConstants_finrank_dimensionlessExponents
-- name    : VaryingConstants.finrank_dimensionlessExponents
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T01:43:57.925327+00:00
-- url     : https://prove2.me/theorems/9865cb93-9cf4-4019-8aa9-b006c7200889
-- title:
--   Number of independent dimensionless combinations is $n-\operatorname{rank}D$
-- statement:
--   Let $D\in\mathbb R^{n\times d}$ be the dimension matrix of $n$ constants with respect to $d$ base units. The space of dimensionless exponent vectors
--   $$\mathcal Z_D=\Big\{a\in\mathbb R^n:\ \sum_{i=1}^n a_iD_{ij}=0\ \text{ for all } j\Big\}$$
--   has dimension
--   $$\dim_{\mathbb R}\mathcal Z_D \;=\; n-\operatorname{rank}D .$$
--
--   This is the dimension count of the Buckingham $\pi$ theorem: from $n$ constants whose dimensions span an $r$-dimensional space one can form exactly $n-r$ independent dimensionless combinations (for $c,G,\hbar$ plus further constants in mechanical units, $r=3$).
-- source:
--   J.-P. Uzan, "Varying Constants, Gravitation and Cosmology", Living Rev. Relativity 14 (2011) 2, http://www.livingreviews.org/lrr-2011-2, §2.1.1, pp. 15–17 ("Natural units", "Fundamental parameters"): with three independent constants as units, all other constants become dimensionless; standard dimension count of the Buckingham π theorem (E. Buckingham, Phys. Rev. 4 (1914) 345, https://doi.org/10.1103/PhysRev.4.345).

import Mathlib
import Definitions.Def_VaryingConstants_units

namespace VaryingConstants

theorem finrank_dimensionlessExponents {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) :
    Module.finrank ℝ (dimensionlessExponents D) = n - D.rank := by sorry

end VaryingConstants
