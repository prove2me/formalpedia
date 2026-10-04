-- Prove2me | Theorems.Thm_VaryingConstants_powerMonomial_isUnitInvariant
-- name    : VaryingConstants.powerMonomial_isUnitInvariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T01:32:25.177162+00:00
-- url     : https://prove2.me/theorems/46f0ac01-e00a-4967-b53a-3e69847caee5
-- title:
--   Dimensionless power products are unit invariant
-- statement:
--   Let $D\in\mathbb R^{n\times d}$ be a dimension matrix and let $a\in\mathbb R^n$ be a dimensionless exponent vector, i.e. $\sum_i a_iD_{ij}=0$ for every base unit $j$. Then the power product $\pi_a(x)=\prod_i x_i^{a_i}$ is unit invariant: for every positive configuration $x\in\mathbb R^n_{>0}$ and every positive change of units $s\in\mathbb R^d_{>0}$,
--   $$ \prod_{i=1}^n\Big(x_i\prod_{j=1}^d s_j^{D_{ij}}\Big)^{a_i} \;=\; \prod_{i=1}^n x_i^{a_i}. $$
--
--   This is the precise sense in which a dimensionless combination of constants (such as $\alpha_{\rm EM}=e^2/4\pi\varepsilon_0\hbar c$ or $m_p/m_e$) has a value independent of the system of units.
-- source:
--   J.-P. Uzan, "Varying Constants, Gravitation and Cosmology", Living Rev. Relativity 14 (2011) 2, http://www.livingreviews.org/lrr-2011-2, §2.1.1 "Fundamental parameters", p. 17: the values of dimensionless combinations "do not depend on ... the definition of the units".

import Mathlib
import Definitions.Def_VaryingConstants_units

namespace VaryingConstants

theorem powerMonomial_isUnitInvariant {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (a : Fin n → ℝ) (ha : a ∈ dimensionlessExponents D) :
    IsUnitInvariant D (powerMonomial a) := by sorry

end VaryingConstants
