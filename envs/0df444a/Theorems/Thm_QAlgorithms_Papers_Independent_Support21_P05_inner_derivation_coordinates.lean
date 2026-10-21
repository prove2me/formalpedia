-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P05_inner_derivation_coordinates
-- name    : QAlgorithms.Papers.Independent.Support21.P05.inner_derivation_coordinates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:32:29.603989+00:00
-- url     : https://prove2.me/theorems/e1c81698-c4ef-4135-af10-d9a2ba298c5a
-- title:
--   Normalized octonion inner derivations have the coordinates (4.9)
-- statement:
--   Work over $\mathbb C$. Write the complex octonions in the Zorn basis as $c=(\alpha^+,\alpha^-,v^+,v^-)$ and $d=(\beta^+,\beta^-,w^+,w^-)$. The product of $(\alpha^+,\alpha^-,v^+,v^-)$ and $(\beta^+,\beta^-,w^+,w^-)$ has diagonal entries $\alpha^+\beta^+-v^+\cdot w^-$ and $\alpha^-\beta^--v^-\cdot w^+$ and off-diagonal entries $\alpha^+w^++\beta^-v^++v^-\wedge w^-$ and $\alpha^-w^-+\beta^+v^-+v^+\wedge w^+$. Here dots are ordinary bilinear contractions and wedges are the oriented cross product. Define $D_{c,d}z=\frac13[[c,d],z]-((cd)z-c(dz))$.
--
--   Then $D_{c,d}$ acts by (4.10) with the following matrix coefficients, whose first component is traceless:
--
--   $$
--   \begin{aligned}
--   a_{ij}&=w_i^+v_j^- -v_i^+w_j^- -\frac{\sum_k(v_k^-w_k^+-v_k^+w_k^-)}3\delta_{ij},\\
--   A^+&=\tfrac13((\alpha^+-\alpha^-)w^+-(\beta^+-\beta^-)v^+-v^-\wedge w^-),\\
--   A^-&=\tfrac13((\alpha^--\alpha^+)w^--(\beta^--\beta^+)v^--v^+\wedge w^+).
--   \end{aligned}
--   $$
--
--   In particular, for the Zorn nilpotent basis vectors $\varepsilon_i^\pm$, the coordinates of $D_{\varepsilon_j^-,\varepsilon_i^+}$ are $(E_{ij}-\delta_{ij}I_3/3,0,0)$, where $E_{ij}$ is the matrix unit. This pins the normalization and index order of the inner derivation coordinates.
--
--   **Formalization Note** The displayed duplicate for $\rho(e_{22})$ on PDF p.12 is corrected to $(-E_{11}+2E_{22}-E_{33})/3$, as implied by its own Cartan expression and by (4.9); independent source verification is recorded in MODERATION-r1.md.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs Part 2: Zorn-type Representations, arXiv:1403.5120v2, PDF p. 12, (4.8)–(4.9): inner derivation coordinates

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P05

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

/-- (4.8)–(4.9), PDF pp. 11–12: normalized inner derivations and every eij.
Printed: rho(e22)=(-E11-E22+2E33)/3, duplicating rho(e33) on PDF p.12.
Changed: rho(e22)=(-E11+2E22-E33)/3, as in the uniform diagonal formula below.
Why: its displayed H1,H2 expression with (4.6), and independently (4.9), give
E22-I3/3. Only the duplicated diagonal is corrected. Source checked in moderation r1. -/
theorem inner_derivation_coordinates :
    (∀ c d : Octonions, Matrix.trace (innerCoordinates c d).1 = 0 ∧
      ∀ z, octonionAction (innerCoordinates c d) z = octonionInner c d z) ∧
    (∀ i j : Fin 3, innerCoordinates (epsilonMinus j) (epsilonPlus i) =
      (matrixUnit i j - (if i = j then (1 / 3 : ℂ) • (1 : Mat3 ℂ) else 0), 0, 0)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P05

end
