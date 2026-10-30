-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_average_worstCase
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.average_worstCase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:32:33.503503+00:00
-- url     : https://prove2.me/theorems/39927c10-6c45-49aa-8182-06e3bcbb98dd
-- title:
--   Theorem 1: average and worst-case fidelities
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   Let $f:\mathrm{SU}(d)\to\mathrm{SU}(e)$ be Borel-measurable and either multiplicative, $f(UV)=f(U)f(V)$, or anti-multiplicative, $f(UV)=f(V)f(U)$. For any process $S$ of one specified class $c$, there is a process $S'$ in the same class and on the same registers such that
--   $$\min_{U\in\mathrm{SU}(d)}F(S',f;U)=\overline F(S,f).$$
--   The minimum is attained. This equates average performance with achievable worst-case performance without changing the allowed class.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 12, Theorem 1: average and worst-case fidelities

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

/-- Theorem 1, PDF pp.12,30: class-preserving average/worst-case equivalence.
The worst case is an attained minimum; normalization is e^{-2}, including in
the appendix's intermediate formulas where the printed factor is omitted. -/
theorem average_worstCase (d e k : ℕ) (hd : 0 < d) (he : 0 < e) (hk : 1 ≤ k)
    (H : HaarLaw d) (f : Target d e) (c : StrategyClass)
    (hf : Homomorphic f ∨ Antihomomorphic f) (S : TransformationProcess k d e)
    (hS : TransformationAdmissible c S) :
    ∃ Snew : TransformationProcess k d e, TransformationAdmissible c Snew ∧
      IsLeast (Set.range (pointFidelity Snew f.value)) (transformationAverage H f.value S) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
