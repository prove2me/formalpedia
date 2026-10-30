-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_transposition_performance_one
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.transposition_performance_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:46:03.164352+00:00
-- url     : https://prove2.me/theorems/0bd44d8f-3bad-4f5e-bb4a-63e57dd61f97
-- title:
--   E.4 / Eq.(121): transposition k=1
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For $d\ge2$, put $P_+=J(I)/d$ and $P_\perp=I-P_+$ on two ordered $d$-dimensional factors. Then
--   $$\Omega_{\rm trans,k=1}=\frac1{d^2}\left((P_+)_{OP}\otimes(P_+)_{IF}+\frac{(P_\perp)_{OP}\otimes(P_\perp)_{IF}}{d^2-1}\right).$$
--   The denominator is the complement rank $d^2-1$, correcting the printed $d-1$ using Eqs.(115),(120). This is the explicit crossed one-query objective.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 34, E.4 / Eq.(121): transposition k=1

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

/-- PDF p.34, Eq.(121): printed d-1 changed to d²-1, the rank of the
orthogonal complement in Eq.(115); at d=2 it is 3, not 1. -/
theorem transposition_performance_one (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d) :
    performance (k := 1) H transposeTarget = ((d : ℂ)^2)⁻¹ •
      (place true (queryTargetBellProjector d false) (queryTargetBellProjector d false) +
        ((d : ℂ)^2-1)⁻¹ • place true (queryTargetBellProjector d true) (queryTargetBellProjector d true)) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
