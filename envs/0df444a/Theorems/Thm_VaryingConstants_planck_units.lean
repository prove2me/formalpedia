-- Prove2me | Theorems.Thm_VaryingConstants_planck_units
-- name    : VaryingConstants.planck_units
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T02:40:47.042373+00:00
-- url     : https://prove2.me/theorems/f6904621-50f4-4a62-8379-1d02798f38bd
-- title:
--   Planck units: $c=G=\hbar=1$ fixes $\ell_P=\sqrt{G\hbar/c^3}$, $m_P=\sqrt{\hbar c/G}$, $t_P=\sqrt{G\hbar/c^5}$
-- statement:
--   Use base units $(L,M,T)$ and the constants $(c,G,\hbar)$ with dimensions $[c]=LT^{-1}$, $[G]=L^3M^{-1}T^{-2}$, $[\hbar]=L^2MT^{-1}$ (dimension matrix $D_{\rm P}$). Let $c,G,\hbar>0$ be their numerical values in some system of units. A vector $s=(s_L,s_M,s_T)$ is a system of natural units for $(c,G,\hbar)$ — i.e. $s$ is positive and
--   $$ c\,s_Ls_T^{-1}=1,\qquad G\,s_L^{3}s_M^{-1}s_T^{-2}=1,\qquad \hbar\,s_L^{2}s_Ms_T^{-1}=1 $$
--   — if and only if
--   $$ s=\Big(\sqrt{\tfrac{c^3}{G\hbar}},\ \sqrt{\tfrac{G}{\hbar c}},\ \sqrt{\tfrac{c^5}{G\hbar}}\Big)=\Big(\tfrac1{\ell_P},\tfrac1{m_P},\tfrac1{t_P}\Big). $$
--
--   Thus the Planck length, mass and time $\ell_P=\sqrt{G\hbar/c^3}$, $m_P=\sqrt{\hbar c/G}$, $t_P=\sqrt{G\hbar/c^5}$ are exactly the units in which $c=G=\hbar=1$.
--
--   **Formalization Note** $s_j$ is the factor multiplying numerical values of quantities of dimension $U_j$; a quantity of dimension $T$ worth $1$ old unit is worth $s_T=1/t_P$ Planck times.
-- source:
--   J.-P. Uzan, "Varying Constants, Gravitation and Cosmology", Living Rev. Relativity 14 (2011) 2, http://www.livingreviews.org/lrr-2011-2, §2.1.1 "Natural units", p. 16: Planck units $t_P=\sqrt{G\hbar/c^5}$, $\ell_P=\sqrt{G\hbar/c^3}$, $m_P=\sqrt{\hbar c/G}$.

import Mathlib
import Definitions.Def_VaryingConstants_units

namespace VaryingConstants

theorem planck_units (c G hbar : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar)
    (s : Fin 3 → ℝ) :
    IsNaturalUnitsFor planckDims id ![c, G, hbar] s ↔
      s = ![Real.sqrt (c ^ 3 / (G * hbar)), Real.sqrt (G / (hbar * c)),
            Real.sqrt (c ^ 5 / (G * hbar))] := by sorry

end VaryingConstants
