-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_pbt_strictGap
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.pbt_strictGap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:43:55.468785+00:00
-- url     : https://prove2.me/theorems/3117a38b-2cea-4fcd-a9ee-fc28fe93c757
-- title:
--   §7 / Eqs.(71),(72): PBT adaptation is suboptimal
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For every $k\ge1$, optimal deterministic qubit PBT and optimal parallel qubit transposition have attained channel fidelities
--   $$F_{\rm ent}^*(\mathrm{PBT};2,k)=\cos^2\!\left(\frac\pi{k+2}\right)<\cos^2\!\left(\frac\pi{k+3}\right)=F_{\rm par}^*(U\mapsto U^T;2,k).$$
--   Thus the PBT adaptation is strictly suboptimal. The comparison uses entanglement fidelity, not the related average pure-state fidelity.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 24, §7 / Eqs.(71),(72): PBT adaptation is suboptimal

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

/-- PDF p.24, Eqs.(71),(72): strict PBT suboptimality in channel fidelity.
The denominators k+2 and k+3 are different. -/
theorem pbt_strictGap (k : ℕ) (hk : 1 ≤ k) (H : HaarLaw 2) :
    IsGreatest (pbtScores k 2) ((Real.cos (Real.pi/((k : ℝ)+2)))^2) ∧
    IsGreatest (scores (k := k) H transposeTarget .parallel)
      ((Real.cos (Real.pi/((k : ℝ)+3)))^2) ∧
    (Real.cos (Real.pi/((k : ℝ)+2)))^2 <
      (Real.cos (Real.pi/((k : ℝ)+3)))^2 := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
