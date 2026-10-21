-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_represented_casimir_eigenvalues
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.represented_casimir_eigenvalues
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:47:25.661978+00:00
-- url     : https://prove2.me/theorems/bfcd2fc6-d7f1-4039-b4fe-c80bce14c100
-- title:
--   Represented first, second and special-unitary Casimir eigenvalues
-- statement:
--   Let $d\ge2$, and let $\pi$ be an actual irreducible smooth finite-dimensional unitary $U(d)$ representation with dominant integral highest weight $m\in\mathbb Z^d$. Write $D=\partial\pi$ for its actual complexified differential and $E_{jk}$ for standard matrix units. Define represented operators
--   $$
--   C_1=\sum_jD(E_{jj}),\quad C_2=\sum_{j,k}D(E_{jk})D(E_{kj}),\quad\widetilde C_2=C_2-\frac1d C_1^2.
--   $$
--   With $q(m)=\sum_jm_j^2+\sum_{j<k}(m_j-m_k)$ and $c(m)=q(m)-(\sum_jm_j)^2/d$,
--   $$
--   C_1=(\sum_jm_j)I,\qquad C_2=q(m)I,\qquad\widetilde C_2=c(m)I,
--   $$
--   and the explicit A8 expression is
--   $$
--   c(m)=\frac1d\left((d-1)\sum_jm_j^2-\sum_{j\ne k}m_jm_k+d\sum_{j<k}(m_j-m_k)\right).
--   $$
--   Setting $F_{jk}=E_{jk}-\delta_{jk}I/d$ gives the consistently indexed traceless quadratic contraction
--   $$
--   \widetilde C_2=\sum_{j,k}D(F_{jk})D(F_{kj}).
--   $$
--   These formulas evaluate actual represented operators, providing the normalization used by the block-coefficient formula.
--
--   **Source Correction** The first $C_1(\pi)$ in printed A7 is $C_2(\pi)$ according to its preceding definition and explicit polynomial. The traceless contraction gives a basis-independent version of A9 with consistent dummy indices; its matrix units form a redundant spanning family rather than a claimed basis.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 14, Appendix A5, Eqs.(A6)–(A9)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF p.14 Eqs.(A6)–(A9): actual represented Casimir eigenvalues, correcting
C_1 to C_2 in A7. A9 is expressed in traceless matrix units
F_jk=E_jk-delta_jk I/d; its inconsistent dummy indices are eliminated. -/
theorem represented_casimir_eigenvalues (d h : ℕ) (hd : 2 ≤ d)
    (pi : SmoothUnitaryRep d h) (m : Fin d → ℤ) (hm : HasHighestWeight pi m) :
    firstCasimir pi = (∑ j : Fin d, (m j : ℂ)) • (1 : Mat h) ∧
    secondCasimir pi = (secondCasimirValue m : ℂ) • (1 : Mat h) ∧
    specialCasimir pi = (casimirValue m : ℂ) • (1 : Mat h) ∧
    casimirValue m = (1 / (d : ℝ)) *
      (((d : ℝ) - 1) * ∑ j : Fin d, (m j : ℝ)^2 -
        (∑ j : Fin d, ∑ k : Fin d, if j ≠ k then (m j : ℝ) * m k else 0) +
        (d : ℝ) * ∑ j : Fin d, ∑ k : Fin d, if j < k then (m j : ℝ) - m k else 0) ∧
    specialCasimir pi = ∑ j : Fin d, ∑ k : Fin d,
      pi.differential (Matrix.single j k 1 - (if j = k then (1 / (d : ℂ)) else 0) • (1 : Mat d)) *
      pi.differential (Matrix.single k j 1 - (if k = j then (1 / (d : ℂ)) else 0) • (1 : Mat d)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
