-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_husimiZeroSurvivesGain
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.husimiZeroSurvivesGain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:36:36.077109+00:00
-- url     : https://prove2.me/theorems/23125e24-9320-4229-8dde-d36645b62488
-- title:
--   §V remark: a Husimi zero survives arbitrary finite amplification
-- statement:
--   Let $\rho$ be any density on the full oscillator space, and define its Husimi function by $Q_\rho(\alpha)=\langle\alpha|\rho|\alpha\rangle$ for normalized coherent states. If $Q_\rho(\alpha_0)=0$, then for every finite real gain $\kappa>1$, the trace-norm amplifier output satisfies
--
--   $$Q_{C_{2,\kappa}(\rho)}(\kappa\alpha_0)=0,\qquad C_{2,\kappa}(\rho)\text{ is nonclassical}.$$
--
--   In particular there exists one input density whose nonclassicality survives every finite gain. That input is chosen before the gain parameter. Classicality is defined by arbitrary positive coherent-state probability measures, so the assertion includes singular classical representations in its exclusion.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 21, §V remark: a Husimi zero survives arbitrary finite amplification

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.21, Husimi-zero remark: every finite gain carries a Q zero alpha0
to k*alpha0 and the output remains nonclassical. The same input can survive
all finite gains; it is quantified before the gain parameter. -/
theorem husimiZeroSurvivesGain :
    CoherentRealized ∧
    (∀ X : FockOperator, IsDensity X → ∀ alpha0 : ℂ, husimiQ X alpha0 = 0 →
      ∀ k : ℝ, 1 < k → AmplifierRealized k ∧ ∃ Y : FockOperator,
        TraceHasSum (fun ell => krausTerm (amplifierKraus k ell) X) Y ∧
        IsDensity Y ∧ husimiQ Y ((k : ℂ) * alpha0) = 0 ∧ ¬ IsClassical Y) ∧
    (∃ X : FockOperator, IsDensity X ∧ ∀ k : ℝ, 1 < k →
      ∃ Y : FockOperator, TraceHasSum (fun ell => krausTerm (amplifierKraus k ell) X) Y ∧
        IsDensity Y ∧ ¬ IsClassical Y) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
