-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P08_nonnegativeSummandsLocalContinuity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P08.nonnegativeSummandsLocalContinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:55:52.125987+00:00
-- url     : https://prove2.me/theorems/c759e114-2b92-44cd-8e04-5a86ce15e547
-- title:
--   Lemma 3: continuity of summands of a nonnegative lower-semicontinuous sum
-- statement:
--   Let $X$ be a metric space and $(f_i)_{i\in K}$ a finite family of lower-semicontinuous functions $X\to[0,+\infty]$. If $x_k\to x_0$ and
--
--   $$
--   \sum_{i\in K}f_i(x_k)\longrightarrow\sum_{i\in K}f_i(x_0)<+\infty,
--   $$
--
--   then, for every $i\in K$,
--
--   $$
--   f_i(x_k)\longrightarrow f_i(x_0)<+\infty.
--   $$
--
--   This transfers finite local continuity of a nonnegative sum to each summand. The empty family is permitted and has no summand conclusion.
-- source:
--   Measures of quantum correlations in infinite-dimensional systems, arXiv:1506.06377v2, PDF p. 8, Lemma 3: continuity of summands of a nonnegative lower-semicontinuous sum

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08

noncomputable section

open Filter

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P08

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

/-- Lemma 3, PDF p.8, with the finite-limit interpretation of Remark 1,
PDF pp.7--8. Extended nonnegative values are retained throughout. -/
theorem nonnegativeSummandsLocalContinuity {X : Type*} [MetricSpace X]
    {K : Type*} [Fintype K] (f : K → X → ℝ≥0∞)
    (hf : ∀ i, LowerSemicontinuous (f i))
    (x : ℕ → X) (x0 : X) (hx : Tendsto x atTop (nhds x0))
    (hFinite : (∑ i, f i x0) < ⊤)
    (hSum : Tendsto (fun k => ∑ i, f i (x k)) atTop (nhds (∑ i, f i x0))) :
    ∀ i, f i x0 < ⊤ ∧ Tendsto (fun k => f i (x k)) atTop (nhds (f i x0)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P08

end
