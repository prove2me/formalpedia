-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_phaseCharacteristic
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.phaseCharacteristic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:26:54.714832+00:00
-- url     : https://prove2.me/theorems/b06d8824-eca3-45d1-a456-ead14c784a31
-- title:
--   Theorem 2: phase-conjugation characteristic semantics
-- statement:
--   Let $\kappa>0$ and let $\rho$ be any density on the full Fock space. Let $\rho'$ be its trace-norm output under the complete countable family $T_\ell(\kappa)$ of Eq. (3.11). Write $D(z)=\exp(za^\dagger-\overline z a)$ for the actual bounded unitary displacement, represented by its explicit Fock coefficients, and $\chi_\rho(z)=\operatorname{tr}[D(z)\rho]$. Then
--
--   $$\chi_{\rho'}(z)=\chi_\rho(-\kappa\overline z)\exp[-(1+\kappa^2)|z|^2/2]\qquad(z\in\mathbb C).$$
--
--   The map is the normalized complete Kraus map on all trace-class inputs; in particular it is completely positive and trace preserving. The characteristic trace pairing is nuclear and absolutely summable. No transformation law is an input hypothesis.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 9, Theorem 2: phase-conjugation characteristic semantics

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Theorem 2, PDF p.9: the complete positive phase-conjugator map implements
the exact characteristic law, with /2 in both Gaussian factors of the source. -/
theorem phaseCharacteristic (k : ℝ) (hk : 0 < k) :
    DisplacementRealized ∧ KrausWellDefined (phaseKraus k) ∧
    ∀ X : FockOperator, IsDensity X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (phaseKraus k ell) X) Y ∧ IsDensity Y ∧
      ∀ z : ℂ, characteristic Y z = characteristic X (-(k : ℂ) * star z) *
        (Real.exp (-(1 + k ^ 2) * Complex.normSq z / 2) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
