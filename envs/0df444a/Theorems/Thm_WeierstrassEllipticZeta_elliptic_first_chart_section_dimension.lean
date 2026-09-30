-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_section_dimension
-- name    : WeierstrassEllipticZeta.elliptic_first_chart_section_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-21T00:14:49.600161+00:00
-- url     : https://prove2.me/theorems/13b6bf3d-1364-403b-8b54-d9e68f950754
-- title:
--   Explicit linear-quadratic bound for first-chart section dimension
-- statement:
--   For every period pair L and natural m,n, the restrictions of bihomogeneous sections of bidegree (m,n) to the first cubic chart span a finite-dimensional complex vector space S_(m,n). Its dimension satisfies
--
--   dim S_(m,n) <= 2*(m+1)*(2*n+1)*(4*n+1).
--
--   When n>=1 this is at most 30*(m+1)*n^2. In particular, for m,n>=1 it is at most 60*m*n^2, while dim S_(0,n)<=30*n^2. The rectangular upper bound includes m=0 and n=0.
--
--   The proof supplies a concrete spanning family t^i*x^j*y^e*u^k with 0<=i<=m, 0<=j<=2n, e in {0,1}, and 0<=k<=4n. The cubic relation reduces every higher y power without increasing the weight that assigns weights 2,3,1 to x,y,u. The normalized homogeneous coordinates have weight at most 4, so bidegree (m,n) fits this family.
--
--   No linear independence, exact dimension, global Hilbert polynomial, or component-multiplicity sum bound is claimed. This is an explicit bound for the relevant section space. A.1 still needs the geometric comparison from local multiplicities to section dimension.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 3, pp. 362-365, section-space/Hilbert-function setup and Lemma 3.2 on primary multiplicities: https://www.numdam.org/item/10.24033/bsmf.2060.pdf. The present elementary supporting calculation uses the explicit first-chart cubic and weights 2,3,1 on x,y,u. It constructs a rectangular spanning family and proves dim S_(m,n)<=2*(m+1)*(2*n+1)*(4*n+1), hence <=30*(m+1)*n^2 for n>=1. It is not a proof of Lemma 3.2 or of the required geometric multiplicity-to-dimension comparison. The frontier reduction turns a C-times-section-dimension bound into the original numeric bound with coefficient 60*C and exponent 2. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X. Global geometric selection and the component multiplicity comparison remain Open.

import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections

open TranscendenceTheory WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_first_chart_section_dimension (L : PeriodPair) (m n : ℕ) :
    Module.Finite ℂ (firstChartSectionSpace L m n) ∧
      Module.finrank ℂ (firstChartSectionSpace L m n) ≤
        2 * (m + 1) * (2 * n + 1) * (4 * n + 1) ∧
      (1 ≤ n → Module.finrank ℂ (firstChartSectionSpace L m n) ≤
        30 * (m + 1) * n ^ 2) := by sorry
