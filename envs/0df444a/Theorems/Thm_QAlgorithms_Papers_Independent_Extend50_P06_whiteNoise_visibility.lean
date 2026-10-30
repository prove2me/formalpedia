-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_whiteNoise_visibility
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.whiteNoise_visibility
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:33:21.752143+00:00
-- url     : https://prove2.me/theorems/7e3cbd4d-a0f5-4793-bd38-6a354346710e
-- title:
--   Theorem 2: white-noise visibility
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   Suppose $e=d$, $f$ is Borel-measurable and multiplicative or anti-multiplicative, $f(\overline U)=\overline{f(U)}$, and its pushforward preserves probability Haar measure. For every process $S$ in class $c$, there are a process $S'$ of the same class and a real number $\eta$ such that, for every $U$,
--   $$S'*J(U)^{\otimes k}=\eta J(f(U))+(1-\eta)\frac{I_P\otimes I_F}{d},\qquad \overline F(S,f)=\eta+\frac{1-\eta}{d^2}.$$
--   Visibility is not required to be nonnegative. This identifies the relevant depolarizing form while also covering $d=1$.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 12, Theorem 2: white-noise visibility

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

/-- Theorem 2, PDF pp.12,30–31: all three target hypotheses are retained.
Visibility is real and may be negative; d=1 does not require division by d²-1. -/
theorem whiteNoise_visibility (d k : ℕ) (hd : 0 < d) (hk : 1 ≤ k)
    (H : HaarLaw d) (f : Target d d) (c : StrategyClass)
    (hf : Homomorphic f ∨ Antihomomorphic f)
    (hconj : ∀ U V : SU d, V.val = U.val.map conj →
      f.value V = (f.value U).map conj)
    (hhaar : Measure.map f.value H.law = Measure.map Subtype.val H.law)
    (S : TransformationProcess k d d) (hS : TransformationAdmissible c S) :
    ∃ (Snew : TransformationProcess k d d) (eta : ℝ), TransformationAdmissible c Snew ∧
      (∀ U : SU d, insertSlots Snew (unitarySlots U.val) =
        (eta : ℂ) • transformationChoi (f.value U) + ((1-eta) / (d : ℝ) : ℝ) •
          (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) ∧
      transformationAverage H f.value S = eta + (1-eta)/(d : ℝ)^2 := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
