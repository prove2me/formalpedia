-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_inversion_qubits
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.inversion_qubits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:40:30.488965+00:00
-- url     : https://prove2.me/theorems/0f07f720-5699-4183-9e93-63caeaad58ba
-- title:
--   §5.2 summary: qubit inversion optimum
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For every $k\ge1$, parallel inversion of qubit unitaries has the attained optimum
--   $$F_{\rm par}^*(U\mapsto U^{-1};2,k)=\cos^2\!\left(\frac\pi{k+3}\right).$$
--   This is the inversion application of the paper's equivalence with unitary estimation.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 22, §5.2 summary: qubit inversion optimum

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

/-- PDF p.22, second summary bullet: exact qubit parallel inversion optimum. -/
theorem inversion_qubits (k : ℕ) (hk : 1 ≤ k) (H : HaarLaw 2) :
    IsGreatest (scores (k := k) H inverseTarget .parallel)
      ((Real.cos (Real.pi/((k : ℝ)+3)))^2) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
