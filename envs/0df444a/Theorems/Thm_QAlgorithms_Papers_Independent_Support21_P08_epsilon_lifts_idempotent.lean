-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_epsilon_lifts_idempotent
-- name    : QAlgorithms.Papers.Independent.Support21.P08.epsilon_lifts_idempotent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:31:31.526998+00:00
-- url     : https://prove2.me/theorems/7035f915-8c33-4bc8-8cfc-dc0d13d8bed5
-- title:
--   Explicit polynomial lifting modulo a nilpotent two-sided ideal
-- statement:
--   Let $H$ be any unital ring, $I$ a two-sided ideal, and $N\ge2$ an integer with $I^N=0$. Define $\varepsilon_N(X)=\sum_{i=0}^{N-1}\binom{2N-1}{i}X^{2N-1-i}(1-X)^i$. If $x^2-x\in I$, then
--
--   $$\varepsilon_N(x)^2=\varepsilon_N(x),\qquad\varepsilon_N(x)-x\in I.$$
--
--   Both the explicit polynomial and its congruence are retained. Two-sidedness is stated directly in the noncommutative ring.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 25, App.2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section RingAppendix

variable {H : Type*} [Ring H]

/-- Appendix Lemma 2.4, PDF p.25. Both explicit epsilon_N idempotence and
its congruence to x are conclusions. N>=2 prevents truncated-exponent issues;
I is genuinely two-sided even when H is noncommutative. -/
theorem epsilon_lifts_idempotent (N : ℕ) (hN : 2 ≤ N) (I : AddSubgroup H)
    (hI : TwoSidedNilpotent I N) (x : H) (hx : x * x - x ∈ I) :
    epsilon N x * epsilon N x = epsilon N x ∧ epsilon N x - x ∈ I := by sorry

end RingAppendix

end QAlgorithms.Papers.Independent.Support21.P08

end
