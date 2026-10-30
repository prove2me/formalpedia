-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_inversion_exponentialAdvantage
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.inversion_exponentialAdvantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:36:05.107606+00:00
-- url     : https://prove2.me/theorems/c80b690a-7a2e-4eca-ac5d-ae1ecd6f486b
-- title:
--   Theorem 6: exponential advantage for unitary inversion
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For every $d\ge2$ and $k\ge1$, every parallel inversion process $S$ and some sequential inversion process $T$ satisfy, respectively,
--   $$\overline F(S,U\mapsto U^{-1})\le1-\frac1{(k+3)^2},\qquad \overline F(T,U\mapsto U^{-1})\ge1-\left(1-\frac1{d^2}\right)^{\lfloor(k+1)/d\rfloor}.$$
--   The floor is the greatest integer at most $(k+1)/d$. The sequential process is deterministic; heralded performance is not an additional hypothesis.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 22, Theorem 6: exponential advantage for unitary inversion

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

/-- Theorem 6, PDF p.22, Eqs.(68),(69). As in Theorem 4, d=1 must be
excluded. The inversion exponent is floor((k+1)/d). -/
theorem inversion_exponentialAdvantage (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k)
    (H : HaarLaw d) :
    (∀ S : TransformationProcess k d d, TransformationAdmissible .parallel S →
      transformationAverage H inverseTarget S ≤ 1 - 1/((k : ℝ)+3)^2) ∧
    ∃ S : TransformationProcess k d d, TransformationAdmissible .sequential S ∧
      1 - (1 - 1/(d : ℝ)^2)^((k+1)/d) ≤ transformationAverage H inverseTarget S := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
