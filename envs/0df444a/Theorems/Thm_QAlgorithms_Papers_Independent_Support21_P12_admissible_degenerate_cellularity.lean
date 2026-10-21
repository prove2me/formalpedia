-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_admissible_degenerate_cellularity
-- name    : QAlgorithms.Papers.Independent.Support21.P12.admissible_degenerate_cellularity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:08:57.908392+00:00
-- url     : https://prove2.me/theorems/45a5b4ee-7224-47cc-a1e4-42d2ba311f1e
-- title:
--   Cellularity and exact rank over arbitrary admissible ground rings
-- statement:
--   Let $S$ be a commutative unital ring, $r\ge1$, and $u_1,\ldots,u_r\in S$. Suppose $\omega_a=\eta_a^+(u_1,\ldots,u_r)$ for every $a\ge0$, evaluating the integral eta polynomials. For every $n\ge0$, the actual degenerate cyclotomic BMW algebra $N_{n,S,r}$ is cellular for the canonical anti-involution, with an indexed cellular basis of size
--
--   $$r^n(2n-1)!!.$$
--
--   In particular it has an S-basis of that size. The double factorial denotes the number of Brauer diagrams, with one empty diagram when $n=0$. The statement needs neither an integral domain nor an inverse of two.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 8, Theorem 3.11

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

universe u

/-- Theorem 3.11, PDF p.8: cellularity AND the stated rank over any
commutative ring, with an indexed basis instead of default-valued finrank.
The diagram count equals (2n-1)!! and has the empty-diagram value one at n=0. -/
theorem admissible_degenerate_cellularity (S : Type u) [CommRing S]
    (omega : ℕ → S) (r : ℕ) (hr : 0 < r) (u : Fin r → S)
    (hadm : RootAdmissible omega u) (n : ℕ) :
    CanonicalCellular S omega .degenerate r u n (some (r ^ n * diagramCount n)) ∧
    Nonempty (Module.Basis (Fin (r ^ n * diagramCount n)) S (Cyclotomic S omega .degenerate r u n)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
