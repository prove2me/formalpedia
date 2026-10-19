-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_krausProductIndependence
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.krausProductIndependence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:39:44.409988+00:00
-- url     : https://prove2.me/theorems/1fd76ef0-ba28-4da7-9fff-6681b60f1e10
-- title:
--   §VIII: algebraic independence of pairwise Kraus products
-- statement:
--   On the full Fock space, take the explicit phase-conjugator family $W_\ell=T_\ell(\kappa)$ with $\kappa>0$, attenuator family $W_\ell=B_\ell(\kappa)$ with $0\le\kappa<1$, or amplifier family $W_\ell=A_\ell(\kappa)$ with $\kappa>1$. In each case the doubly indexed family is algebraically linearly independent:
--
--   $$\{W_m^\dagger W_n:(m,n)\in\mathbb N^2\}\text{ is linearly independent over }\mathbb C.$$
--
--   Linear independence tests finite linear combinations. The self-dual phase case $\kappa=1$ is included; the loss endpoint $\kappa=0$ is included, and the identity loss/gain endpoints are excluded. This is the algebraic assertion from the source, and does not define or assume extremality of a normal channel.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 29, §VIII: algebraic independence of pairwise Kraus products

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF pp.27–29 Eqs.(8.1)–(8.8): algebraic independence of all pairwise
Kraus products, in each stated discrete family. D(1) and loss k=0 are included.
This assertion is not used as a definition of channel extremality. 
Printed: Section VIII includes the attenuator endpoint kappa=0 and discusses the identity endpoint; the phase paragraph excludes kappa=1 before its next paragraph includes D(1).
Changed: State independence for phase kappa>0 including 1, loss 0<=kappa<1 including 0, and gain kappa>1. Keep the full Nat x Nat index set.
Why: At loss kappa=0, B_m^dagger B_n=|m><n|, so independence survives. At loss/gain kappa=1, positive-index Kraus operators are zero, so independence fails. Phase kappa=1 has no such zero operators. These are precisely the necessary endpoint corrections; no infinite-dimensional extremality criterion is asserted.
-/
theorem krausProductIndependence :
    (∀ k : ℝ, 0 < k → LinearIndependent ℂ
      (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (phaseKraus k p.1)).comp
        (phaseKraus k p.2))) ∧
    (∀ k : ℝ, 0 ≤ k → k < 1 → AttenuatorRealized k ∧ LinearIndependent ℂ
      (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (attenuatorKraus k p.1)).comp
        (attenuatorKraus k p.2))) ∧
    (∀ k : ℝ, 1 < k → AmplifierRealized k ∧ LinearIndependent ℂ
      (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (amplifierKraus k p.1)).comp
        (amplifierKraus k p.2))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
