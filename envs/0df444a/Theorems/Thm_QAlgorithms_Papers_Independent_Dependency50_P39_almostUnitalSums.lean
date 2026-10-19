-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_almostUnitalSums
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.almostUnitalSums
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:26:08.845981+00:00
-- url     : https://prove2.me/theorems/31179507-3e1a-4673-8157-928e79931310
-- title:
--   Eqs.(3.12),(5.6): almost-unital Gaussian families
-- statement:
--   On $H=\ell^2(\mathbb N;\mathbb C)$, let $W_\ell(\kappa)$ be respectively the source's phase-conjugator family $T_\ell$ for $\kappa>0$, attenuator family $B_\ell$ for $0<\kappa\le1$, or amplifier family $A_\ell$ for $\kappa\ge1$. For each family,
--
--   $$\sum_{\ell\ge0}W_\ell^\dagger W_\ell=I,\qquad \sum_{\ell\ge0}W_\ell W_\ell^\dagger=\kappa^{-2}I.$$
--
--   Both equalities use strong operator convergence on every Hilbert vector. In particular the unital parameter is $\kappa=1$. The identity here belongs to the bounded-operator algebra; it is not an input density. These equalities explain the scalar normalization of the dual families.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 7, Eqs.(3.12),(5.6): almost-unital Gaussian families

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF pp.7,19 Eqs.(3.12),(5.6): the three almost-unital operator sums.
The reciprocal-square factors are bounded-operator statements; I is not a state. -/
theorem almostUnitalSums :
    (∀ k : ℝ, 0 < k → KrausComplete (phaseKraus k) ∧
      StrongHasSum (fun ell => (phaseKraus k ell).comp
        (ContinuousLinearMap.adjoint (phaseKraus k ell)))
        (((k⁻¹) ^ 2 : ℂ) • (1 : FockOperator))) ∧
    (∀ k : ℝ, 0 < k → k ≤ 1 → AttenuatorRealized k ∧
      KrausComplete (attenuatorKraus k) ∧
      StrongHasSum (fun ell => (attenuatorKraus k ell).comp
        (ContinuousLinearMap.adjoint (attenuatorKraus k ell)))
        (((k⁻¹) ^ 2 : ℂ) • (1 : FockOperator))) ∧
    (∀ k : ℝ, 1 ≤ k → AmplifierRealized k ∧
      KrausComplete (amplifierKraus k) ∧
      StrongHasSum (fun ell => (amplifierKraus k ell).comp
        (ContinuousLinearMap.adjoint (amplifierKraus k ell)))
        (((k⁻¹) ^ 2 : ℂ) • (1 : FockOperator))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
