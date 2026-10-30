-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_transposition_exponentialAdvantage
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.transposition_exponentialAdvantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:31:41.58944+00:00
-- url     : https://prove2.me/theorems/2d85b732-447d-4a67-92e1-19ee6ba0ab67
-- title:
--   Theorem 4: exponential advantage for unitary transposition
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For every $d\ge2$ and $k\ge1$, every parallel process $S$ obeys the first bound and some sequential process $T$ obeys the second:
--   $$\overline F(S,U\mapsto U^T)\le1-\frac1{(k+3)^2},\qquad \overline F(T,U\mapsto U^T)\ge1-\left(1-\frac1{d^2}\right)^{\lceil k/d\rceil}.$$
--   The ceiling is the least integer at least $k/d$. This gives the paper's polynomial versus exponential approach to perfect fidelity.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 20, Theorem 4: exponential advantage for unitary transposition

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P06

namespace QAlgorithms.Papers.Independent.Extend50.P06

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

-- Exact accepted interfaces; no duplicate SU subtype or ambient-coordinate Haar law.

open QAlgorithms.Papers.Independent.Information100.P47 (Mat)

open QAlgorithms.Papers.Independent.Claimed50.P21 (SU HaarLaw)

open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P06.targetMatrixMeasurable

/-- Theorem 4, PDF p.20, Eqs.(57),(58). The printed “any dimension” is
restricted to d≥2, as required by the proof's SU(2) inclusion and by the d=1
counterexample. The sequential exponent is ceiling(k/d), not floor((k+1)/d). -/
theorem transposition_exponentialAdvantage (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k)
    (H : HaarLaw d) :
    (∀ S : TransformationProcess k d d, TransformationAdmissible .parallel S →
      transformationAverage H transposeTarget S ≤ 1 - 1/((k : ℝ)+3)^2) ∧
    ∃ S : TransformationProcess k d d, TransformationAdmissible .sequential S ∧
      1 - (1 - 1/(d : ℝ)^2)^((k+d-1)/d) ≤ transformationAverage H transposeTarget S := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
