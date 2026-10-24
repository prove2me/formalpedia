-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_lemma8
-- name    : QAlgorithms.Papers.Independent.Support50.P38.lemma8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:00:16.503993+00:00
-- url     : https://prove2.me/theorems/c773dc2f-918c-4b9d-918d-71eb4f7937d5
-- title:
--   Simultaneous row and aggregate sampling on a type class
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $n\ge1$, and $T$ a joint exact $n$-type with marginal types $R,S$. Let $u_R,u_S$ be the uniform type-class laws and $V_T$ the uniform reverse conditional-type channel. Fix $0<\epsilon<1/2$ and positive integers $M,N$ satisfying
--
--   $$
--   M>\frac{2\ln2}{\epsilon^2}\frac{|\mathcal T_R||\mathcal T_S|}{|\mathcal T_T|}\log_2(4N|\mathcal T_R|),\qquad
--   NM>\frac{2\ln2}{\epsilon^2}|\mathcal T_S|\log_2(4|\mathcal T_S|).
--   $$
--   There is one array $Y_j^{(s)}\in\mathcal T_S$, $s\in[N],j\in[M]$, for which, pointwise as functions,
--
--   $$
--   (1-\epsilon)u_R\le\frac1M\sum_j V_T(\cdot|Y_j^{(s)})\le(1+\epsilon)u_R\quad\text{for every }s,
--   $$
--   $$
--   (1-\epsilon)u_S\le\frac1{NM}\sum_{s,j}\delta_{Y_j^{(s)}}\le(1+\epsilon)u_S.
--   $$
--   Repeated samples are allowed. The simultaneous array is the combinatorial interface for channel compression.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 4, Lemma 8

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Lemma 8, PDF p.4: one sampling array simultaneously satisfies every row bound and
the aggregate empirical-law bound. Sampling is with replacement. The small relative-error
range 0 < epsilon < 1/2 is inherited from Lemma 5, used in the proof. -/
theorem lemma8 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] {n : ℕ} (hn : 0 < n) (t : ExactType (A × B) n)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (m seeds : ℕ) (hm : 0 < m) (hs : 0 < seeds)
    (hrow : (2 * Real.log 2 / epsilon ^ 2) *
      (((typeWords t.left).card : ℝ) * (typeWords t.right).card / (typeWords t).card) *
      Real.logb 2 (4 * seeds * (typeWords t.left).card : ℝ) < m)
    (hall : (2 * Real.log 2 / epsilon ^ 2) * (typeWords t.right).card *
      Real.logb 2 (4 * (typeWords t.right).card : ℝ) < (seeds : ℝ) * m) :
    ∃ ys : Fin seeds → Fin m → SourceWord B n,
      (∀ s j, ys s j ∈ typeWords t.right) ∧
      (∀ s x,
        (1 - epsilon) * typeUniform t.left x ≤ (∑ j, typeReverse t (ys s j) x) / m ∧
        (∑ j, typeReverse t (ys s j) x) / m ≤ (1 + epsilon) * typeUniform t.left x) ∧
      (∀ y,
        (1 - epsilon) * typeUniform t.right y ≤
          (∑ s, ∑ j, if ys s j = y then (1 : ℝ) else 0) / ((seeds : ℝ) * m) ∧
        (∑ s, ∑ j, if ys s j = y then (1 : ℝ) else 0) / ((seeds : ℝ) * m) ≤
          (1 + epsilon) * typeUniform t.right y) := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
