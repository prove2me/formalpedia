-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_phaseContinuousRankOne
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.phaseContinuousRankOne
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:29:01.81945+00:00
-- url     : https://prove2.me/theorems/5297457a-682a-49a4-bc6a-ee27e0e242eb
-- title:
--   Eq.(3.42): coherent-state rank-one Kraus realization
-- statement:
--   Let $\kappa>0$ and $\alpha\in\mathbb C$. Write $|\alpha\rangle$ for the normalized coherent state, and let $T_\ell(\kappa)$ be the phase-conjugator Kraus family. Define
--
--   $$T'_\alpha(\kappa)=\frac{1}{\sqrt{1+\kappa^2}}\left|\frac{\alpha}{\sqrt{1+\kappa^{-2}}}\right\rangle\left\langle\frac{\overline\alpha}{\sqrt{1+\kappa^2}}\right|.$$
--
--   Every $T'_\alpha$ has rank one and is the operator-norm sum $\sum_{\ell\ge0}\langle\ell|\alpha\rangle T_\ell(\kappa)$. With measure $d^2\alpha/\pi$, this continuous Kraus representation gives the same output as the countable family on every trace-class input. Its trace norms and its matrix-coefficient integrands are integrable. The channel is entanglement breaking in the operational sense, including arbitrary ancillary entangled inputs. The two different square-root denominators and the conjugated bra are essential.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 13, Eq.(3.42): coherent-state rank-one Kraus realization

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Eq.(3.42), PDF pp.12–13: the coherent-state isometry produces a rank-one
continuous Kraus realization. The integral is specified by integrable matrix
coefficients and integrable trace norms on every trace-class input. -/
theorem phaseContinuousRankOne (k : ℝ) (hk : 0 < k) :
    CoherentRealized ∧ IsCountableEntanglementBreaking (phaseKraus k) ∧
    (∀ alpha : ℂ,
      Module.rank ℂ (LinearMap.range (coherentPhaseKraus k alpha).toLinearMap) = 1 ∧
      HasSum (fun ell => coherentCoefficient alpha ell • phaseKraus k ell)
        (coherentPhaseKraus k alpha)) ∧
    ∀ X : FockOperator, IsTraceClass X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (phaseKraus k ell) X) Y ∧
      (∀ alpha, IsTraceClass (krausTerm (coherentPhaseKraus k alpha) X)) ∧
      Integrable (fun alpha => nuclearTraceNorm (krausTerm (coherentPhaseKraus k alpha) X))
        coherentMeasure ∧
      ∀ m n : ℕ,
        Integrable (fun alpha => krausTerm (coherentPhaseKraus k alpha) X (fockKet n) m)
          coherentMeasure ∧
        Y (fockKet n) m = ∫ alpha,
          krausTerm (coherentPhaseKraus k alpha) X (fockKet n) m ∂coherentMeasure := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
