-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_coherent_vacuum_lattice
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.coherent_vacuum_lattice
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:47:24.18124+00:00
-- url     : https://prove2.me/theorems/d404e206-f590-4575-8a59-1a325ac37bba
-- title:
--   §IV (29): coherent-state lattice representation
-- statement:
--   Let $\alpha>0$ and let $g(q)=\pi^{-1/4}e^{-q^2/2}$ be the normalized oscillator vacuum. The ordered displacement projection in (29), including its BCH phase, has the weak expansion
--
--   $$\sum_{s,t\in\mathbb Z}e^{2\pi itq/\alpha}g(q-s\alpha)=C\sum_{k\in\mathbb Z}\delta(q-k\alpha),\qquad C\ne0.$$
--
--   The weak summands are absolutely summable on Schwartz tests. Their coherent-state centers are $(s\alpha,2\pi t/\alpha)$ and their fundamental cell has area $2\pi$. Starting from any coherent state rigidly translates the centers and gives a scalar multiple of this same comb; the scalar is nonzero whenever that projection is nonzero.
--
--   The conclusion does not assert a nonzero projection for every possible starting state.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 5, §IV (29): coherent-state lattice representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section IV (29), PDF p.5: vacuum projection gives the nonzero equal-weight coherent lattice.
Only the explicitly constructed vacuum projection is asserted, not every starting state. -/
theorem coherent_vacuum_lattice (alpha : ℝ) (ha : 0 < alpha) :
    (∀ q0 p0 : ℝ, ∃ C : ℂ,
      (∀ f : SchwartzMap ℝ ℂ,
        projectedCoherent alpha q0 p0 f = C * ∑' k : ℤ, f (k * alpha)) ∧
      (projectedCoherent alpha q0 p0 ≠ 0 → C ≠ 0)) ∧
    ∃ C : ℂ, C ≠ 0 ∧
      (∀ f : SchwartzMap ℝ ℂ,
        Summable (fun st : ℤ × ℤ => ∫ q : ℝ, coherentLatticeWave alpha st.1 st.2 q * f q) ∧
        (∑' st : ℤ × ℤ, ∫ q : ℝ, coherentLatticeWave alpha st.1 st.2 q * f q) =
          C * ∑' k : ℤ, f (k * alpha)) ∧
      alpha * (2 * Real.pi / alpha) = 2 * Real.pi := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
