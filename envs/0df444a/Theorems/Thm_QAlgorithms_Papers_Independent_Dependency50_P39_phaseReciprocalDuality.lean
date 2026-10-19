-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_phaseReciprocalDuality
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.phaseReciprocalDuality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:25:35.237981+00:00
-- url     : https://prove2.me/theorems/84995cb6-1a3a-4813-8490-178e6ed7e711
-- title:
--   Theorem 1: reciprocal phase-conjugation duality
-- statement:
--   Let $\kappa>0$. On the full Fock space $H=\ell^2(\mathbb N;\mathbb C)$, let $T_\ell(\kappa)$ be the explicit phase-conjugator Kraus operators of Eq. (3.11), with index $\ell\in\mathbb N$. Then
--
--   $$\kappa T_\ell(\kappa)^\dagger=T_\ell(\kappa^{-1})\qquad(\ell\ge0).$$
--
--   The normalized adjoint family is strongly complete and defines the same trace-class map as the reciprocal phase-conjugator family: both sums converge in trace norm to the same operator for every trace-class input. This identifies the normalization required for reciprocal duality.
--
--   The operators act on $H=\ell^2(\mathbb N;\mathbb C)$, with orthonormal basis $|n\rangle$ for $n\ge0$. The fixed source families are
--   $$
--   \begin{aligned}
--   B_\ell(b)&=\sum_{m\ge0}\sqrt{\binom{m+\ell}{\ell}}\,\sqrt{1-b^2}^{\,\ell}b^m|m\rangle\langle m+\ell|,\\
--   A_\ell(g)&=g^{-1}\sum_{m\ge0}\sqrt{\binom{m+\ell}{\ell}}\,\sqrt{1-g^{-2}}^{\,\ell}g^{-m}|m+\ell\rangle\langle m|,\\
--   T_\ell(t)&=(\sqrt{1+t^2})^{-1}\sum_{n=0}^{\ell}\sqrt{\binom\ell n}(\sqrt{1+t^2})^{-n}(\sqrt{1+t^{-2}})^{-(\ell-n)}|\ell-n\rangle\langle n|.
--   \end{aligned}
--   $$
--   Here $0\le b\le1$, $g\ge1$, and $t>0$. Endpoints are $B_\ell(0)=|0\rangle\langle\ell|$, $B_0(1)=A_0(1)=I$, and $B_\ell(1)=A_\ell(1)=0$ for $\ell>0$. When used, $T_\ell(0)=|0\rangle\langle\ell|$ is specified separately. Infinite operator sums that define a channel are interpreted in trace norm on trace-class inputs.
-- source:
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 7, Theorem 1: reciprocal phase-conjugation duality

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Theorem 1, PDF p.7 Eq.(3.13): reciprocal phase-conjugation duality.
The common trace-class map uses k T_ell(k)†, including the necessary scalar. -/
theorem phaseReciprocalDuality (k : ℝ) (hk : 0 < k) :
    (∀ ell, (k : ℂ) • ContinuousLinearMap.adjoint (phaseKraus k ell) =
      phaseKraus k⁻¹ ell) ∧
    KrausEquivalent (fun ell => (k : ℂ) •
      ContinuousLinearMap.adjoint (phaseKraus k ell)) (phaseKraus k⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
