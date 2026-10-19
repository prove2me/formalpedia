-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_gainLossDuality
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.gainLossDuality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:34:58.91918+00:00
-- url     : https://prove2.me/theorems/621905a5-9e23-438a-811a-ea1b609286cb
-- title:
--   Theorem 9: amplifier–attenuator normalized duality
-- statement:
--   Let $\kappa>1$. Let $A_\ell(\kappa)$ be the amplifier family of Eq. (5.5), and $B_\ell(\kappa^{-1})$ the reciprocal attenuator family of Eq. (4.6). For every $\ell\in\mathbb N$,
--
--   $$\kappa A_\ell(\kappa)^\dagger=B_\ell(\kappa^{-1}),\qquad
--   \kappa^{-1}B_\ell(\kappa^{-1})^\dagger=A_\ell(\kappa).$$
--
--   Both normalized adjoint families are strongly complete and give exactly their respective reciprocal channel maps on every trace-class input, with trace-norm convergence. Thus both directions of duality include their correct scalar, rather than using a raw adjoint map as a trace-preserving channel.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 19, Theorem 9: amplifier–attenuator normalized duality

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Theorem 9, PDF p.19 Eq.(5.7): both normalized amplifier/attenuator dualities.
The operator identities fix the inconsistent reciprocal prose immediately nearby. 
Printed: The prose after Eq.(5.6) uses the reciprocal loss scalar inconsistently, while Eq.(5.7) gives A(kappa)^dagger = kappa^(-1) B(kappa^(-1)).
Changed: Use kappa A(kappa)^dagger = B(kappa^(-1)) and kappa^(-1) B(kappa^(-1))^dagger = A(kappa), with kappa>1.
Why: These are the normalized identities fixed by the displayed coefficients and Eq.(5.7); their vacuum entries are respectively 1 and kappa^(-1). No channel or parameter is changed.
-/
theorem gainLossDuality (k : ℝ) (hk : 1 < k) :
    AmplifierRealized k ∧ AttenuatorRealized k⁻¹ ∧
    (∀ ell, (k : ℂ) • ContinuousLinearMap.adjoint (amplifierKraus k ell) =
      attenuatorKraus k⁻¹ ell) ∧
    (∀ ell, (k⁻¹ : ℂ) • ContinuousLinearMap.adjoint (attenuatorKraus k⁻¹ ell) =
      amplifierKraus k ell) ∧
    KrausEquivalent (fun ell => (k : ℂ) •
      ContinuousLinearMap.adjoint (amplifierKraus k ell)) (attenuatorKraus k⁻¹) ∧
    KrausEquivalent (fun ell => (k⁻¹ : ℂ) •
      ContinuousLinearMap.adjoint (attenuatorKraus k⁻¹ ell)) (amplifierKraus k) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
