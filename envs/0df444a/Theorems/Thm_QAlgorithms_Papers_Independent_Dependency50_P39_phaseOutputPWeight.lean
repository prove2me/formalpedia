-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_phaseOutputPWeight
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.phaseOutputPWeight
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:29:51.565025+00:00
-- url     : https://prove2.me/theorems/7bae561e-0a5b-4b2a-8754-96670bb6a60f
-- title:
--   Theorem 5: output P weight, nonclassicality and entanglement breaking
-- statement:
--   Let $\kappa>0$, let $\rho$ be any density on the full Fock space, and let $\rho'=D_\kappa(\rho)$ be the trace-norm output of the explicit countable $T_\ell(\kappa)$ family. For normalized coherent states define $Q_\rho(\alpha)=\langle\alpha|\rho|\alpha\rangle$. Relative to $d^2\alpha/\pi$, the output has the nonnegative normalized diagonal weight
--
--   $$P_{\rho'}(\alpha)=\kappa^{-2}Q_\rho(\kappa^{-1}\overline\alpha),\qquad
--   \rho'=\int_{\mathbb C}P_{\rho'}(\alpha)|\alpha\rangle\langle\alpha|\,\frac{d^2\alpha}{\pi}.$$
--
--   All coefficient integrals are genuine integrals. Consequently every output is classical, and applying the channel to one subsystem of an arbitrary bipartite density produces a separable state, with separability defined by trace-norm closed convex mixtures of product densities. This gives both nonclassicality breaking and entanglement breaking.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 13, Theorem 5: output P weight, nonclassicality and entanglement breaking

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Theorem 5, PDF p.13, with (3.24) on p.9 and (3.43) on p.13:
the exact output P density is the conjugated scaled input Q function.
Entanglement breaking is operational on arbitrary bipartite densities. -/
theorem phaseOutputPWeight (k : ℝ) (hk : 0 < k) :
    CoherentRealized ∧ KrausWellDefined (phaseKraus k) ∧
    IsCountableEntanglementBreaking (phaseKraus k) ∧
    ∀ X : FockOperator, IsDensity X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (phaseKraus k ell) X) Y ∧
      IsClassical Y ∧ IsPositivePWeight Y
        (fun alpha => (k⁻¹) ^ 2 * husimiQ X ((k⁻¹ : ℂ) * star alpha)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
