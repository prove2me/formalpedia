-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_homomorphic_performance
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.homomorphic_performance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:38:17.000056+00:00
-- url     : https://prove2.me/theorems/22c3ed22-efdd-4bcc-96dd-48240be010cc
-- title:
--   §4 / Eq.(31), A.1 / Eq.(77): commutant expansion
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   Let $f:\mathrm{SU}(d)\to\mathrm{SU}(e)$ be a Borel-measurable homomorphism. Let $\{P_i\}_{i=1}^n$ be any nonzero Hilbert–Schmidt orthogonal basis of the commutant of $\overline U^{\otimes k}\otimes f(U)$. Set $h_i=\operatorname{tr}(P_i^\dagger P_i)>0$. Then
--   $$\Omega=\frac1{e^2}\sum_{i=1}^n\frac{\overline{(P_i)_{IP}}\otimes(P_i)_{OF}}{h_i}.$$
--   The labels specify query wires before the target wire within each block; the expression is reindexed to the global $P,I,O,F$ ordering. No unit-norm assumption on the basis is made. This explicitly evaluates the performance operator.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 26, §4 / Eq.(31), A.1 / Eq.(77): commutant expansion

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

/-- PDF pp.14–15,26, Eqs.(31),(77): orthogonal commutant expansion in IP/OF
order with squared Hilbert–Schmidt norms, including the dagger specified p.15. -/
theorem homomorphic_performance (d e k n : ℕ) (hd : 0 < d) (he : 0 < e)
    (hk : 1 ≤ k) (H : HaarLaw d) (f : Target d e) (hf : Homomorphic f)
    (P : Fin n → Matrix (QueryRegister k d × Fin e) (QueryRegister k d × Fin e) ℂ)
    (hP : OrthogonalCommutantBasis (targetTensorRepresentation f.value false) P) :
    performance H f.value = commutantExpansion false P := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
