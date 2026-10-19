-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_amplifierHusimiScaling
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.amplifierHusimiScaling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:35:50.790047+00:00
-- url     : https://prove2.me/theorems/eb2a62de-de64-4299-a8fb-436b42948898
-- title:
--   Theorem 10: amplifier scales Husimi Q
-- statement:
--   Let $\kappa>1$, let $\rho$ be any density on the full Fock space, and define $Q_\rho(\alpha)=\langle\alpha|\rho|\alpha\rangle$ using normalized coherent states. The complete countable amplifier family defines a completely positive trace-preserving map, and
--
--   $$Q_{C_{2,\kappa}(\rho)}(\alpha)=\kappa^{-2}Q_\rho(\kappa^{-1}\alpha).$$
--
--   The planar measure is $d^2\alpha/\pi$. Its actual Weyl characteristic law is also retained:
--
--   $$\chi_{C_{2,\kappa}(\rho)}(z)=\chi_\rho(\kappa z)\exp[-(\kappa^2-1)|z|^2/2].$$
--
--   Here $\chi_\rho(z)=\operatorname{tr}[D(z)\rho]$, with the unitary displacement and trace pairing realized from their concrete Fock coefficients. Every Kraus sum converges in trace norm.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 21, Theorem 10: amplifier scales Husimi Q

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Theorem 10, PDF pp.20–21: Q scaling, the complete CP Kraus realization,
and its characteristic law. Q has no pi factor; the planar measure is d²alpha/pi. -/
theorem amplifierHusimiScaling (k : ℝ) (hk : 1 < k) :
    CoherentRealized ∧ DisplacementRealized ∧ AmplifierRealized k ∧
    KrausWellDefined (amplifierKraus k) ∧
    ∀ X : FockOperator, IsDensity X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (amplifierKraus k ell) X) Y ∧ IsDensity Y ∧
      (∀ alpha : ℂ, husimiQ Y alpha = (k⁻¹) ^ 2 * husimiQ X ((k⁻¹ : ℂ) * alpha)) ∧
      (∀ z : ℂ, characteristic Y z = characteristic X ((k : ℂ) * z) *
        (Real.exp (-(k ^ 2 - 1) * Complex.normSq z / 2) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
