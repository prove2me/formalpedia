-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_attenuatorInputExamples
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.attenuatorInputExamples
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:32:13.888985+00:00
-- url     : https://prove2.me/theorems/3d3e1a69-f65a-4036-a3ab-e6dafb7fed83
-- title:
--   Eqs.(4.17)–(4.19): thermal, Fock and Poissonian input laws
-- statement:
--   Let $0<\kappa<1$. For finite thermal parameter $a\ge1$, define $\rho_{\mathrm{th}}(a)=\frac{2}{a+1}\sum_{n\ge0}((a-1)/(a+1))^n|n\rangle\langle n|$. Let $\rho_\lambda=e^{-\lambda}\sum_{n\ge0}(\lambda^n/n!)|n\rangle\langle n|$ for $\lambda\ge0$. Then
--
--   $$C_{1,\kappa}(\rho_{\mathrm{th}}(a))=\rho_{\mathrm{th}}(\kappa^2a+1-\kappa^2),\qquad
--   C_{1,\kappa}(\rho_\lambda)=\rho_{\kappa^2\lambda},$$
--
--   and
--
--   $$C_{1,\kappa}(|n\rangle\langle n|)=\sum_{j=0}^n\binom nj(1-\kappa^2)^{n-j}\kappa^{2j}|j\rangle\langle j|.$$
--
--   All inputs and outputs are actual normalized trace-class densities, and all Kraus sums converge in trace norm. Iterating the real thermal-parameter recurrence sends every $a\ge1$ to $1$. This is a parameter limit, not the deferred arbitrary-state attraction claim.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 16, Eqs.(4.17)–(4.19): thermal, Fock and Poissonian input laws

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Eqs.(4.17)–(4.19), PDF pp.15–16: thermal, Fock and Poisson laws, plus
thermal-parameter convergence. The vacuum exception is preserved. -/
theorem attenuatorInputExamples (k : ℝ) (hk : 0 < k) (hku : k < 1) :
    AttenuatorRealized k ∧ KrausWellDefined (attenuatorKraus k) ∧
    (∀ a : ℝ, 1 ≤ a → ThermalRealized a ∧
      ThermalRealized (attenuatorThermalParameter k a) ∧
      TraceHasSum (fun ell => krausTerm (attenuatorKraus k ell) (thermalDensity a))
        (thermalDensity (attenuatorThermalParameter k a)) ∧
      Tendsto (fun N : ℕ => ((attenuatorThermalParameter k)^[N]) a) atTop (nhds 1)) ∧
    (∀ lambda : ℝ, 0 ≤ lambda → PoissonRealized lambda ∧ PoissonRealized (k ^ 2 * lambda) ∧
      TraceHasSum (fun ell => krausTerm (attenuatorKraus k ell) (poissonDensity lambda))
        (poissonDensity (k ^ 2 * lambda))) ∧
    (∀ n : ℕ, TraceHasSum (fun ell => krausTerm (attenuatorKraus k ell) (fockDyad n n))
      (∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n j : ℝ) * (1 - k ^ 2) ^ (n - j) * k ^ (2 * j) : ℂ) •
          fockDyad j j)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
