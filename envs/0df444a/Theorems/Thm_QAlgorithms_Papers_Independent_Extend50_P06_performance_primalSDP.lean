-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_performance_primalSDP
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.performance_primalSDP
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:37:30.772523+00:00
-- url     : https://prove2.me/theorems/c0e5cda8-b2c1-4984-8550-2d31f473fe9b
-- title:
--   §3.2 / Eqs.(24)–(26): performance operator and primal SDP
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For a Borel-measurable target $f:\mathrm{SU}(d)\to\mathrm{SU}(e)$, define
--   $$\Omega=\frac1{e^2}\int J(f(U))_{PF}\otimes\overline{J(U)}_{IO}^{\otimes k}\,dU.$$
--   For each of the parallel, sequential and general domains $\mathcal S_c$, every admissible $S$ has $\overline F(S,f)=\operatorname{Re}\operatorname{tr}(S\Omega)$. There are finitely many real linear functionals $A_j$ and real constants $b_j$ such that $S\in\mathcal S_c$ exactly when $S\succeq0$ and $A_j(S)=b_j$ for all $j$. Moreover,
--   $$\max_{S\in\mathcal S_c}\overline F(S,f)=\max_{S\in\mathcal S_c}\operatorname{Re}\operatorname{tr}(S\Omega),$$
--   and these maxima are attained. Thus the optimization is a primal SDP; measure-and-prepare is not included in this claim.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 13, §3.2 / Eqs.(24)–(26): performance operator and primal SDP

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

/-- PDF pp.13–14, Eqs.(24)–(26): trace objective and an exact finite linear
constraint description of each PSD process domain. Measure-and-prepare is
excluded. The maximum is attained and has the same value for both objectives. -/
theorem performance_primalSDP (d e k : ℕ) (hd : 0 < d) (he : 0 < e) (hk : 1 ≤ k)
    (H : HaarLaw d) (f : Target d e) (c : StrategyClass) :
    (∀ S : TransformationProcess k d e, TransformationAdmissible c S →
      transformationAverage H f.value S = (Matrix.trace (S * performance H f.value)).re) ∧
    (∃ n : ℕ, ∃ A : Fin n → (TransformationProcess k d e →ₗ[ℝ] ℝ), ∃ b : Fin n → ℝ,
      ∀ S : TransformationProcess k d e, TransformationAdmissible c S ↔ S.PosSemidef ∧ ∀ j, A j S = b j) ∧
    ∃ S : TransformationProcess k d e, TransformationAdmissible c S ∧
      IsGreatest (scores (k := k) H f.value c) (Matrix.trace (S * performance H f.value)).re := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
