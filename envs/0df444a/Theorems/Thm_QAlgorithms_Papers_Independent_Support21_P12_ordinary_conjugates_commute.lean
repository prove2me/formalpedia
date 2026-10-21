-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_ordinary_conjugates_commute
-- name    : QAlgorithms.Papers.Independent.Support21.P12.ordinary_conjugates_commute
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:11:09.18992+00:00
-- url     : https://prove2.me/theorems/2a424f2a-092d-4c6c-a861-d4730094be5a
-- title:
--   Distant generators commute with both conjugate affine families
-- statement:
--   Let $S$ be a commutative unital ring and let $W_n$ be either the affine or a positive-degree cyclotomic ordinary BMW algebra. The parameters $\rho,q$ are units satisfying (2.1), and cyclotomic roots are units. Put $y'_1=y''_1=y_1$, $y'_{j+1}=g_jy'_jg_j^{-1}$, and $y''_{j+1}=g_j^{-1}y''_jg_j$. For valid indices $1\le i<n$ and $1\le j\le n$ with $j\notin\{i,i+1\}$,
--
--   $$[e_i,y'_j]=[g_i,y'_j]=[e_i,y''_j]=[g_i,y''_j]=0.$$
--
--   The bracket means $[a,b]=ab-ba$. No torsion freedom, admissibility or semi-admissibility is required for these presentation identities.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 12, Lemma 5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Lemma 5.6, PDF p.12, for ANY ordinary affine or cyclotomic BMW algebra.
Neither Assumption 5.1 nor Assumption 5.3 is imposed here. -/
theorem ordinary_conjugates_commute (S : Type*) [CommRing S] (omega : ℕ → S)
    (rho q : Sˣ) (hcompat : (↑(rho⁻¹) : S) - ↑rho =
      ((↑(q⁻¹) : S) - ↑q) * (omega 0 - 1)) (n : ℕ) :
    let K : Kind S omega := .ordinary rho q hcompat
    ConjugateCommutation n (ag S omega K n) (agi S omega K n) (ae S omega K n) (ay S omega K n) ∧
    (∀ (r : ℕ) (u : Fin r → S), ValidRoots K u →
      ConjugateCommutation n (cg S omega K r u n) (cgi S omega K r u n)
        (ce S omega K r u n) (cy S omega K r u n)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
