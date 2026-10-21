-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_degenerate_spanning_cardinalities
-- name    : QAlgorithms.Papers.Independent.Support21.P12.degenerate_spanning_cardinalities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:13:12.179429+00:00
-- url     : https://prove2.me/theorems/534b9da8-f5ba-4546-8469-e32917977b03
-- title:
--   Spanning cardinalities for semi-admissible degenerate BMW algebras
-- statement:
--   Let $S$ be an integral domain, with arbitrary degenerate parameters $\Omega,u_1,\ldots,u_r$ of positive degree. Suppose the whole left ideal $N_{2,S,r}e_1$ is torsion free and Assumption 5.3 holds for $0<d<r$, including d-semi-admissibility and $p_0(y_1)e_1=0$ for $p_0(T)=\prod_{i=1}^d(T-u_i)$. For $n\ge2$, let $J_n=N_ne_{n-1}N_n$ and let $b'(n)$ count Brauer diagrams with a horizontal edge. There are spanning sets of cardinalities
--
--   $$d^n b'(n)\text{ for }J_n,\qquad d^n b'(n)+r^n n!\text{ for }N_n.$$
--
--   No basis conclusion is inserted. This statement does not assume the incorrect inhomogeneous associated-graded equation printed in Lemma 5.9.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 15, Lemma 5.10

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Lemma 5.10, PDF p.15. Only the cardinality conclusion is used; the false
inhomogeneous associated-graded formula printed as Lemma 5.9 is NOT assumed. -/
theorem degenerate_spanning_cardinalities (S : Type*) [CommRing S] [IsDomain S]
    (omega : ℕ → S) (r : ℕ) (u : Fin r → S) (hr : 0 < r)
    (htor : IdealTorsionFree S omega .degenerate r u)
    (d : ℕ) (h : d ≤ r) (hsplit : SplitSemi S omega .degenerate r u d h)
    (n : ℕ) (hn : 2 ≤ n) :
    HasSpanningSetCard (contractionIdeal (S := S) (ce S omega .degenerate r u n (n-2)))
      (d ^ n * horizontalDiagramCount n) ∧
    HasSpanningSetCard (⊤ : Submodule S (Cyclotomic S omega .degenerate r u n))
      (d ^ n * horizontalDiagramCount n + r ^ n * n.factorial) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
