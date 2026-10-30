-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_conjugation_performance_one
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.conjugation_performance_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:44:51.321639+00:00
-- url     : https://prove2.me/theorems/95d317fb-e0c2-4b41-8086-ff7ba5376c74
-- title:
--   E.3 / Eq.(118): conjugation k=1
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   Let $F$ swap two $d$-dimensional factors and $P_s=(I+F)/2$, $P_a=(I-F)/2$. For $d\ge2$, the conjugation performance operator at $k=1$ is
--   $$\Omega=\frac1{d^2}\left(\frac{(P_s)_{IP}\otimes(P_s)_{OF}}{(d^2+d)/2}+\frac{(P_a)_{IP}\otimes(P_a)_{OF}}{(d^2-d)/2}\right).$$
--   The second prepared projector is antisymmetric; the printed symmetric label is corrected using the preceding commutant formula. This gives an explicit SDP objective.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 33, E.3 / Eq.(118): conjugation k=1

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

/-- PDF p.33, Eq.(118), corrected second OF “sym” to “asym” by Eq.(117).
d≥2 keeps the antisymmetric denominator nonzero. -/
theorem conjugation_performance_one (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d) :
    performance (k := 1) H conjugateTarget = ((d : ℂ)^2)⁻¹ •
      (((((d : ℂ)^2+d)/2)⁻¹) • place false (queryTargetPairProjector d false) (queryTargetPairProjector d false) +
       (((d : ℂ)^2-d)/2)⁻¹ • place false (queryTargetPairProjector d true) (queryTargetPairProjector d true)) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
