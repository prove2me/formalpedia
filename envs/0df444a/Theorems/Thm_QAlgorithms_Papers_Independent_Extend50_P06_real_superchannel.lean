-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_real_superchannel
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.real_superchannel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:41:21.701313+00:00
-- url     : https://prove2.me/theorems/8d8c1d2c-e65e-43a8-81d7-87278e4b6530
-- title:
--   §6 footnote 8: real optimization
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For a Borel-measurable target, suppose its actual performance operator is real in the computational basis: $\overline\Omega=\Omega$. For any admissible $S$ in a specified class, the explicitly constructed matrix
--   $$S_{\mathbb R}=\frac{S+\overline S}{2}$$
--   is admissible in the same class, all its entries are real, and $\operatorname{tr}(S_{\mathbb R}\Omega)=\operatorname{tr}(S\Omega)$. Bars denote entrywise conjugation. This permits optimization over real process matrices.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 22, §6 footnote 8: real optimization

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

/-- PDF p.22, footnote 8: entrywise conjugation, not adjoint. With a real
performance matrix, real symmetrization preserves the domain and objective. -/
theorem real_superchannel (d e k : ℕ) (hd : 0 < d) (he : 0 < e) (hk : 1 ≤ k)
    (H : HaarLaw d) (f : Target d e) (c : StrategyClass) (S : TransformationProcess k d e)
    (hS : TransformationAdmissible c S) (hreal : (performance (k := k) H f.value).map conj =
      performance (k := k) H f.value) :
    let Sreal := (2 : ℂ)⁻¹ • (S + S.map conj)
    TransformationAdmissible c Sreal ∧ (∀ x y, (Sreal x y).im = 0) ∧
      Matrix.trace (Sreal * performance H f.value) =
        Matrix.trace (S * performance H f.value) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
