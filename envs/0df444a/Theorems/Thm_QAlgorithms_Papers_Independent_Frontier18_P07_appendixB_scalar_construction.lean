-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_appendixB_scalar_construction
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.appendixB_scalar_construction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:02:55.012388+00:00
-- url     : https://prove2.me/theorems/4716db5c-5b4f-4218-832b-77923227b5c3
-- title:
--   Appendix B: explicit scalar sequence used by the counterexample
-- statement:
--   On $[0,1]$, let $f(t)=t(1-\ln t)$ with $f(0)=0$, and let $f^{-1}$ be its inverse there. For $x\ge1$, set $g(x)=xf^{-1}((\ln2)/x)$ and $H(x)=h_2(g(x))+g(x)\log_2x$, where $h_2(q)=-q\log_2q-(1-q)\log_2(1-q)$ uses $0\log_2 0=0$. Then
--
--   $$0\le g(x)\le1,\quad\lim_{x\to\infty}g(x)=0,\quad H\text{ is strictly increasing on }[1,\infty),\quad H(x)<1,\quad\lim_{x\to\infty}H(x)=1.$$
--
--   Thus $q_n=g(n)$ for positive integers $n$ tends to zero while its entropy profile increases to one bit. This is the scalar ingredient of Appendix B’s example, without asserting the deferred channel counterexample itself.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 15, Appendix B: explicit scalar sequence used by the counterexample

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix B, PDF pp.15-16: the explicit scalar construction gives an
increasing extendedEntropyNats profile bounded above by one bit, converging to one, while
g(x) tends to zero. Only x>=1 is in the domain of the inverse formula. -/
theorem appendixB_scalar_construction :
    (∀ x ∈ Set.Ici (1 : ℝ), scalarG x ∈ Set.Icc (0 : ℝ) 1) ∧
    Tendsto scalarG atTop (𝓝 0) ∧
    StrictMonoOn scalarH (Set.Ici (1 : ℝ)) ∧
    (∀ x ∈ Set.Ici (1 : ℝ), scalarH x < 1) ∧
    Tendsto scalarH atTop (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
