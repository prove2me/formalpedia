-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P06_weightVectorIntertwiners
-- name    : QAlgorithms.Papers.Independent.Support21.P06.weightVectorIntertwiners
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:38:39.730995+00:00
-- url     : https://prove2.me/theorems/b251627a-beb1-447c-ba91-d8c09ba9e561
-- title:
--   Intertwiners of ordinary weight vectors and their nonvanishing
-- statement:
--   Let $n\ge1$, let $q\in\mathbb C^\times$ be not a root of unity, and let $M$ be a complex affine Hecke module with the generator relations of §1. Let $t=(t_1,\ldots,t_n)\in(\mathbb C^\times)^n$ and let $m\in M$ satisfy $x_jm=t_jm$ for every $j$. No finite-dimensionality is needed for this ordinary-weight assertion. Fix $1\le i<n$ with $t_i\ne t_{i+1}$, and define
--   $$
--   \tau_i m=\left(T_i-\frac{(q-q^{-1})t_{i+1}}{t_{i+1}-t_i}\right)m.
--   $$
--   Then $\tau_i m$ belongs to the weight space of $s_it$, including the possibility that it is zero, and
--   $$
--   \tau_i\tau_i m=\frac{(qt_{i+1}-q^{-1}t_i)(qt_i-q^{-1}t_{i+1})}{(t_{i+1}-t_i)(t_i-t_{i+1})}\,m.
--   $$
--   The outer intertwiner is evaluated at $s_it$. Consequently,
--   $$
--   m\ne0,\quad t_i\notin\{q^2t_{i+1},q^{-2}t_{i+1}\}\quad\Longrightarrow\quad\tau_i m\ne0.
--   $$
--   This describes the ordinary weight vectors transported by a local intertwiner and identifies when transport cannot annihilate a nonzero vector.
--
--   **Formalization Note** The denominator in the printed (3.7a) has its sign reversed. The displayed denominator follows the defining operator in Proposition 3.2. Nonzero input is explicit only in the nonvanishing implication.
-- source:
--   Skew shape representations are irreducible, arXiv:math/0401326v2, PDF p. 10, Weight vectors 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent nextPosition)

attribute [local instance] Classical.propDecidable

/-- Weight-vector assertions (3.7a–b), PDF p.10.
Printed: t_i-t_(i+1) in (3.7a). Changed: t_(i+1)-t_i.
Why: the definition on p.8, Proposition 3.2, and the two-box row T_i=q
all require this sign. The membership assertion includes zero; nonvanishing
requires the input vector to be nonzero, as used on p.16.
This correction awaits independent moderation. -/
theorem weightVectorIntertwiners
    (n : ℕ) (hn : 0 < n) (q : ℂ) (hq : GenericParameter q)
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (A : AffineAction n q V) (t : Fin n → ℂ) (ht : TorusWeight t)
    (i : Adjacent n) (hi : t i.val ≠ t (nextPosition i))
    (m : V) (hm : InWeightSpace A t m) :
    tauWeight A t i m = A.t i m -
      ((q - q⁻¹) * t (nextPosition i) / (t (nextPosition i) - t i.val)) • m ∧
    InWeightSpace A (permuteWeight (simplePerm i) t) (tauWeight A t i m) ∧
    tauWeight A (permuteWeight (simplePerm i) t) i (tauWeight A t i m) =
      tauSquareScalar q t i • m ∧
    (m ≠ 0 → t i.val ≠ q ^ 2 * t (nextPosition i) →
      t i.val ≠ (q⁻¹) ^ 2 * t (nextPosition i) → tauWeight A t i m ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Support21.P06

end
