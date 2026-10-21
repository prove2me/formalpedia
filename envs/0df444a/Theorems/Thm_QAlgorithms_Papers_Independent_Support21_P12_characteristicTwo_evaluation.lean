-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_characteristicTwo_evaluation
-- name    : QAlgorithms.Papers.Independent.Support21.P12.characteristicTwo_evaluation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:08:17.027007+00:00
-- url     : https://prove2.me/theorems/ad7f11e0-406a-4340-a478-db3a26696f8d
-- title:
--   Characteristic-two evaluation of integral q and eta polynomials
-- statement:
--   Let $S$ be a commutative unital ring of characteristic two, let $r\ge1$, and choose $u_1,\ldots,u_r\in S$. The polynomials $q_a$ are the Schur q-polynomials from the product $\prod_i(1+u_it)/(1-u_it)$, and $p_a(u)=\sum_i u_i^a$. Interpret $q_a/2$ and $\eta_a^+$ as integer polynomials before evaluation. Then
--
--   $$q_a(u)=0,\quad (q_a/2)(u)=p_a(u)\quad(a\ge1),\qquad \eta_0^+(u)=\delta_{r\text{ odd}},\quad \eta_a^+(u)=p_a(u)\quad(a\ge1).$$
--
--   These identities retain the information lost by evaluating q before halving, and apply to the admissibility sequence in characteristic two.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 6, Example 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Example 3.4, PDF p.6. Half q and eta are evaluated only after integral
lifting. The power-sum equality is restricted to positive a. -/
theorem characteristicTwo_evaluation (S : Type*) [CommRing S] [CharP S 2]
    (r : ℕ) (hr : 0 < r) (u : Fin r → S) :
    (∀ a : ℕ, 1 ≤ a →
      evalIntegral u (schurQ r a) = 0 ∧
      evalIntegral u (halfSchurQ r a) = ∑ i : Fin r, u i ^ a) ∧
    evalIntegral u (etaIntegral r 0 true) = (if Odd r then 1 else 0) ∧
    (∀ a : ℕ, 1 ≤ a → evalIntegral u (etaIntegral r a true) = ∑ i : Fin r, u i ^ a) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
