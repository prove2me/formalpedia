-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P16_degenerateCyclotomic_rightIdeal
-- name    : QAlgorithms.Papers.Independent.Renew46.P16.degenerateCyclotomic_rightIdeal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:21:08.051258+00:00
-- url     : https://prove2.me/theorems/ca39000f-fed6-43aa-8c16-97ee2b2106a9
-- title:
--   Lemma 6.13 — degenerate cyclotomic BMW right ideal stability
-- statement:
--   Let $S$ be a commutative unital ring with a sequence $\Omega$, let $r\ge1$, and choose $u_1,\ldots,u_r\in S$. Let $W_n$ be the quotient in Definition 6.8, obtained by imposing $\prod_{j=1}^r(x_1-u_j)=0$ on $W_n^{\mathrm{aff}}$. For every $n\ge2$,
--
--   $$W_ne_{n-1}=W_{n-1}e_{n-1}.$$
--
--   The smaller algebra is its canonical generator image in $W_n$, and both sides are additive $S$-submodules. This is right multiplication by $e_{n-1}$ on the two coefficient algebras; admissibility is not required.
-- source:
--   On Cellular Algebras with Jucys Murphy Elements, arXiv:0907.3459v2, PDF p. 25, Lemma 6.13

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 6.13, PDF p.25. No admissibility or characteristic hypothesis is
added to the cyclotomic quotient, whose degree r is positive. -/
theorem degenerateCyclotomic_rightIdeal (S : Type*) [CommRing S] (omega : ℕ → S)
    (n r : ℕ) (u : Fin r → S) (hn : 2 ≤ n) (hr : 1 ≤ r) :
    rightProductSpan S (Set.univ : Set (CyclotomicBMW S omega n r u))
      (cyclotomicE S omega n r u (n - 2)) =
    rightProductSpan S (cyclotomicLevel S omega n r u (n - 1) :
      Set (CyclotomicBMW S omega n r u))
      (cyclotomicE S omega n r u (n - 2)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P16

end
