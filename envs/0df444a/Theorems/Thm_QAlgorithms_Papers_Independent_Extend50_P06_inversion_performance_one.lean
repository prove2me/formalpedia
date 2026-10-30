-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_inversion_performance_one
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.inversion_performance_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:47:24.104503+00:00
-- url     : https://prove2.me/theorems/cee0912a-5c3c-44fd-a0a0-da24dd4fc95c
-- title:
--   E.5 / Eq.(124): inversion k=1
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   Let $F$ swap two $d$-dimensional factors and $P_s=(I+F)/2$, $P_a=(I-F)/2$. For $d\ge2$, the inversion performance operator at $k=1$ is
--   $$\Omega=\frac1{d^2}\left(\frac{(P_s)_{OP}\otimes(P_s)_{IF}}{(d^2+d)/2}+\frac{(P_a)_{OP}\otimes(P_a)_{IF}}{(d^2-d)/2}\right).$$
--   The second prepared projector is antisymmetric; the printed symmetric label is corrected using the preceding commutant formula. This gives an explicit SDP objective.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 34, E.5 / Eq.(124): inversion k=1

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

/-- PDF p.34, Eq.(124): printed “trans” changed to inversion and second IF
“sym” to “asym”, both uniquely fixed by Eq.(123). -/
theorem inversion_performance_one (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d) :
    performance (k := 1) H inverseTarget = ((d : ℂ)^2)⁻¹ •
      (((((d : ℂ)^2+d)/2)⁻¹) • place true (queryTargetPairProjector d false) (queryTargetPairProjector d false) +
       (((d : ℂ)^2-d)/2)⁻¹ • place true (queryTargetPairProjector d true) (queryTargetPairProjector d true)) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
