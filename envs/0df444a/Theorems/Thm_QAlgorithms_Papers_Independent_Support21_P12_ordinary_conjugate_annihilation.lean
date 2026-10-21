-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_ordinary_conjugate_annihilation
-- name    : QAlgorithms.Papers.Independent.Support21.P12.ordinary_conjugate_annihilation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:11:49.889638+00:00
-- url     : https://prove2.me/theorems/7d4c7260-b4ff-482e-a511-ba9a483fd8eb
-- title:
--   The minimal polynomial annihilates distant contractions on both sides
-- statement:
--   Let $S$ be an integral domain and let $W_{n,S,r}$ be the actual ordinary cyclotomic BMW algebra, with unit parameters satisfying (2.1). Assume the whole two-strand left ideal is torsion free and Assumption 5.3 holds for $0<d<r$: the parameters are d-semi-admissible and $p_0(T)=\prod_{i=1}^d(T-u_i)$ annihilates $e_1$ at $y_1$. Define $y'_1=y''_1=y_1$, $y'_{j+1}=g_jy'_jg_j^{-1}$, and $y''_{j+1}=g_j^{-1}y''_jg_j$. For $1\le i<n$ and $1\le j\le n$ with $j\ne i+1$,
--
--   $$p_0(y'_j)e_i=e_ip_0(y'_j)=0,\qquad p_0(y''_j)e_i=e_ip_0(y''_j)=0.$$
--
--   All four annihilation equations are retained, with the single exceptional index stated explicitly.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 12, Lemma 5.7

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Lemma 5.7, PDF pp.12--13. The sole exceptional index is j=i+1;
BOTH multiplication orders and BOTH conjugation families are asserted. -/
theorem ordinary_conjugate_annihilation (S : Type*) [CommRing S] [IsDomain S]
    (omega : ℕ → S) (rho q : Sˣ) (hcompat : (↑(rho⁻¹) : S) - ↑rho =
      ((↑(q⁻¹) : S) - ↑q) * (omega 0 - 1)) (r : ℕ) (u : Fin r → S)
    (d : ℕ) (h : d ≤ r)
    (hu : ValidRoots (.ordinary rho q hcompat) u)
    (htor : IdealTorsionFree S omega (.ordinary rho q hcompat) r u)
    (hsplit : SplitSemi S omega (.ordinary rho q hcompat) r u d h)
    (n i j : ℕ) (hi : i+1 < n) (hj : j < n) (hex : j ≠ i+1) :
    let K : Kind S omega := .ordinary rho q hcompat
    ∀ rev : Bool,
      let z := Polynomial.aeval
        (conjugateY (cg S omega K r u n) (cgi S omega K r u n) (cy S omega K r u n) rev j)
        (rootPolynomial (firstRoots u h))
      z * ce S omega K r u n i = 0 ∧ ce S omega K r u n i * z = 0 := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
