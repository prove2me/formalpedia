-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_phaseExplicitKraus
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.phaseExplicitKraus
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:24:42.524853+00:00
-- url     : https://prove2.me/theorems/7f1e6852-8226-4ce9-92da-97853237fd57
-- title:
--   §III Eq.(3.11): explicit phase-conjugation Kraus family
-- statement:
--   Let $\kappa>0$. The explicit bounded operators $T_\ell(\kappa)$ on $\ell^2(\mathbb N;\mathbb C)$ are a strongly complete countable Kraus family, with a trace-norm output on every trace-class input. For every density $\rho$, its output $\rho'$ satisfies
--
--   $$\chi_{\rho'}(z)=\chi_\rho(-\kappa\overline z)\exp[-(1+\kappa^2)|z|^2/2],$$
--
--   where $\chi_\rho(z)=\operatorname{tr}[D(z)\rho]$ uses the actual unitary Weyl displacement. Their Fock coefficients are real, and
--
--   $$\operatorname{tr}(T_\ell^\dagger T_r)=0\quad(\ell\ne r),\qquad
--   \operatorname{rank}T_\ell=\ell+1,\qquad
--   \operatorname{tr}(T_\ell^\dagger T_\ell)=(1+\kappa^2)^{-1}.$$
--
--   The formula below specifies the full source family without a Fock cutoff. The characteristic law identifies the actual channel rather than assuming it.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 6, §III Eq.(3.11): explicit phase-conjugation Kraus family

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Eq.(3.11), PDF p.6, and the explicit rank/norm discussion on p.12:
complete phase-conjugator family, Gaussian identity, real matrix coefficients,
trace orthogonality, rank ell+1, and equal Hilbert–Schmidt norms. -/
theorem phaseExplicitKraus (k : ℝ) (hk : 0 < k) :
    DisplacementRealized ∧ KrausWellDefined (phaseKraus k) ∧
    (∀ X : FockOperator, IsDensity X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (phaseKraus k ell) X) Y ∧ IsDensity Y ∧
      ∀ z : ℂ, characteristic Y z = characteristic X (-(k : ℂ) * star z) *
        (Real.exp (-(1 + k ^ 2) * Complex.normSq z / 2) : ℂ)) ∧
    (∀ ell m n, (phaseKraus k ell (fockKet n) m).im = 0) ∧
    (∀ ell r, IsTraceClass ((ContinuousLinearMap.adjoint (phaseKraus k ell)).comp
      (phaseKraus k r))) ∧
    (∀ ell r, ell ≠ r →
      fockTrace ((ContinuousLinearMap.adjoint (phaseKraus k ell)).comp
        (phaseKraus k r)) = 0) ∧
    (∀ ell, Module.rank ℂ (LinearMap.range (phaseKraus k ell).toLinearMap) =
      (ell + 1 : ℕ)) ∧
    (∀ ell, fockTrace ((ContinuousLinearMap.adjoint (phaseKraus k ell)).comp
      (phaseKraus k ell)) = (((1 + k ^ 2)⁻¹ : ℝ) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
