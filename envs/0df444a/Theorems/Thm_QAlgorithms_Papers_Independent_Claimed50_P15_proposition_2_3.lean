-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_proposition_2_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.proposition_2_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:41:09.245723+00:00
-- url     : https://prove2.me/theorems/97981944-2ca7-4b7c-af5b-897bf1289a2a
-- title:
--   Proposition 2.3
-- statement:
--   Let $t$ range over an arbitrary unbounded subset $I$ of positive reals. On possibly varying measurable spaces let $P_t$ be finite nonzero measures, let $X_t$ be measurable and real, and let positive $w_t\to\infty$. Suppose, for real $a<b$, that $e(s)=\lim_{t\to\infty}w_t^{-1}\log\int e^{sX_t}\,dP_t$ is finite on $[a,b]$ and continuous there. Let $\phi(\theta)=\sup_{s\in[a,b]}(s\theta-e(s))$ and $D_\pm$ be the one-sided slopes.
--
--   $$\begin{aligned}0\in[a,b)&\implies\limsup_t w_t^{-1}\log P_t(X_t>\theta w_t)\le\begin{cases}-\phi(\theta)&\theta\ge D_+e(0),\\ e(0)&\theta<D_+e(0);\end{cases}\\0\in(a,b]&\implies\limsup_t w_t^{-1}\log P_t(X_t<\theta w_t)\le\begin{cases}-\phi(\theta)&\theta\le D_-e(0),\\ e(0)&\theta>D_-e(0).\end{cases}\end{aligned}$$
--
--   The events are strict tails; zero event mass has logarithm $-\infty$.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 8, Proposition 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 2.3, both strict tails and correct endpoint sides,
arXiv:1109.3804v2, PDF p.8, (2.5)--(2.6). -/
theorem proposition_2_3 (F : LDFamily) (a b : ℝ) (hab : a < b)
    (e : ℝ → ℝ) (hLD : HasLD F a b e) :
    (a ≤ 0 ∧ 0 < b → ∀ theta : ℝ,
      Filter.limsup (scaledEvent F (upperTail F theta)) (indexFilter F) ≤
        if rightSlope b e 0 ≤ (theta : EReal) then ((-legendre a b e theta : ℝ) : EReal) else (e 0 : EReal)) ∧
    (a < 0 ∧ 0 ≤ b → ∀ theta : ℝ,
      Filter.limsup (scaledEvent F (lowerTail F theta)) (indexFilter F) ≤
        if (theta : EReal) ≤ leftSlope a e 0 then ((-legendre a b e theta : ℝ) : EReal) else (e 0 : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
