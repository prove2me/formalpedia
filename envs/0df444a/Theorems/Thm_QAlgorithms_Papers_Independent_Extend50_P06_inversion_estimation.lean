-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_inversion_estimation
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.inversion_estimation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:35:18.053157+00:00
-- url     : https://prove2.me/theorems/2ae7f2b5-f613-4e7d-94da-174f08df424b
-- title:
--   Theorem 5: inversion, transposition, and estimation
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For every $d\ge1$ and $k\ge1$, a parallel measure-and-prepare process attains the optimal inversion average fidelity, and normalized parallel unitary estimation has the same attained optimum:
--   $$F_{\rm par}^*(U\mapsto U^{-1};d,k)=F_{\rm est}^*(d,k).$$
--   Estimation uses fixed unitary guesses scored by $\operatorname{tr}[J(V)J(U)]/d^2$. This is the inversion counterpart of Theorem 3. The second sentence's printed transposition is corrected to inversion using the proof and Eqs.(62)–(67).
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 21, Theorem 5: inversion, transposition, and estimation

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

/-- Theorem 5, PDF p.21. Printed second sentence repeats “transposition”;
changed to inversion, as fixed by Eqs.(62)–(67) and the concluding proof
paragraph. The printed reference to Lemma 2 at Eq.(64) means Theorem 2. -/
theorem inversion_estimation (d k : ℕ) (hd : 0 < d) (hk : 1 ≤ k)
    (H : HaarLaw d) :
    ∃ S : TransformationProcess k d d, TransformationAdmissible .parallel S ∧ ParallelMeasurePrepare S ∧
      IsGreatest (scores (k := k) H inverseTarget .parallel) (transformationAverage H inverseTarget S) ∧
      ∃ n : ℕ, ∃ E : Estimator k d n,
        IsGreatest (estimationScores (k := k) H) (estimateScore H E) ∧
        transformationAverage H inverseTarget S = estimateScore H E := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
