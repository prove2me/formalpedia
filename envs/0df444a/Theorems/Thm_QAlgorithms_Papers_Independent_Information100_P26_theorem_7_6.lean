-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_theorem_7_6
-- name    : QAlgorithms.Papers.Independent.Information100.P26.theorem_7_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:47:17.602983+00:00
-- url     : https://prove2.me/theorems/d2b7a60f-714e-4855-8316-596194013169
-- title:
--   Theorem 7.6: seven equivalent continuous-time channel properties
-- statement:
--   Let $(\tau_t=e^{tL})_{t\ge0}$ be a continuous semigroup of unital CP, trace-preserving channels on $M_d$, $d\ge1$, with its actual generator $L$. The following seven properties are equivalent: eventual MTD, eventual EB, eventual PPT, eventual 2-copositivity, $\mathcal P(L)=\mathbb C I_d$, primitivity, and
--   $$\lim_{t\to\infty}\tau_t=\delta_d.$$
--   Here $\mathcal P(L)=\operatorname{span}_{\mathbb C}\{X:L(X)=iaX\text{ for some }a\in\mathbb R\}$. Eventual properties mean $\exists t_0>0\ \forall t\ge t_0$. Primitivity means existence of a unique strictly positive stationary density matrix for the adjoint semigroup. The limit is in the finite-dimensional superoperator topology. This is the continuous-time capstone; trace preservation is retained in addition to unital complete positivity.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 28, Theorem 7.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Theorem 7.6, PDF pp.28,29. -/
theorem theorem_7_6 {d : ℕ} (hd : 0 < d) (s : ChannelSemigroup d) :
    (EventuallyTime MTD s ↔ EventuallyTime EB s) ∧
    (EventuallyTime MTD s ↔ EventuallyTime PPT s) ∧
    (EventuallyTime MTD s ↔ EventuallyTime TwoCopositive s) ∧
    (EventuallyTime MTD s ↔ poissonBoundary s = scalars d) ∧
    (EventuallyTime MTD s ↔ SemigroupPrimitive s) ∧
    (EventuallyTime MTD s ↔ Tendsto s.time atTop (nhds (depolarizing d))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
