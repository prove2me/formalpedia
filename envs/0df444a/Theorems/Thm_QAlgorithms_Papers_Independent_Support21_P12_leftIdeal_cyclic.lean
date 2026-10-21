-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_leftIdeal_cyclic
-- name    : QAlgorithms.Papers.Independent.Support21.P12.leftIdeal_cyclic
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:06:36.383896+00:00
-- url     : https://prove2.me/theorems/bc3d8779-0529-4f12-b27c-2b0e98017792
-- title:
--   The two-strand contraction left ideal is cyclically spanned
-- statement:
--   Let $S$ be a commutative unital ring, $r\ge1$, and let $A_2$ be either actual cyclotomic BMW presentation with parameters $\Omega,u_1,\ldots,u_r$. In the ordinary case, $\rho,q$ and the roots are units and satisfy relation (2.1). Write $y_1,e_1$ for its affine and contraction generators. Then
--
--   $$A_2e_1=\operatorname{span}_S\{y_1^je_1:0\le j<r\}.$$
--
--   No admissibility is assumed. The equality describes the whole left ideal, rather than the two-sided contraction ideal.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 4, Lemma 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Lemma 2.6, PDF p.4, both actual presented flavors and no admissibility. -/
theorem leftIdeal_cyclic (S : Type*) [CommRing S] (omega : ℕ → S)
    (K : Kind S omega) (r : ℕ) (u : Fin r → S) (hu : ValidRoots K u) :
    leftIdealSpan (S := S) (ce S omega K r u 2 0) =
      Submodule.span S (Set.range (cyclicFamily (S := S)
        (cy S omega K r u 2) (ce S omega K r u 2 0) r)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
