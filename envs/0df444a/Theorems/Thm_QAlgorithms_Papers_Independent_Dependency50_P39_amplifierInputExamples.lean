-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_amplifierInputExamples
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.amplifierInputExamples
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:37:48.397019+00:00
-- url     : https://prove2.me/theorems/76eda593-1949-433c-9b7d-e5e7e0a64603
-- title:
--   Eqs.(5.20)–(5.23): thermal, Fock and Poissonian inputs
-- statement:
--   Let $\kappa>1$ and let $\rho_{\mathrm{th}}(a)$, $a\ge1$, and $\rho_\lambda$, $\lambda\ge0$, denote respectively the normalized thermal and phase-averaged coherent densities. The amplifier sends the thermal parameter to $\kappa^2a+\kappa^2-1$. Its Fock law is
--
--   $$C_{2,\kappa}(|n\rangle\langle n|)=\sum_{\ell\ge0}\binom{n+\ell}{\ell}(1-\kappa^{-2})^\ell\kappa^{-(2n+2)}|n+\ell\rangle\langle n+\ell|.$$
--
--   The Poisson input output has normalized diagonal weights
--
--   $$p_r=e^{-\lambda}\kappa^{-2}\sum_{j=0}^r\frac{\lambda^j}{j!}\binom rj(1-\kappa^{-2})^{r-j}\kappa^{-2j}.$$
--
--   Both descriptions are trace-norm output identities for actual density operators. The Poisson output has finite first and second photon moments and variance strictly greater than its mean. The factor $\kappa^{-2}$ omitted in printed Eq. (5.23) is restored from Eq. (5.22), which the source substitutes; this correction requires independent moderation.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 22, Eqs.(5.20)–(5.23): thermal, Fock and Poissonian inputs

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Eqs.(5.20)–(5.23), PDF pp.21–22: thermal, Fock and Poisson amplifier
laws. The Poisson output restores k^-2 from (5.22), which (5.23) omits; this
source correction requires independent moderation. 
Printed: Eq.(5.23), PDF p.22, prints the Poisson average without the overall kappa^(-2) factor present in Eq.(5.22).
Changed: Multiply every output coefficient in Eq.(5.23) by kappa^(-2); retain its Poisson weights and all other coefficients.
Why: The source explicitly substitutes Eq.(5.22), which carries this factor. At lambda=0, the printed geometric weights sum to kappa^2; the corrected weights sum to one for every kappa>1.
-/
theorem amplifierInputExamples (k : ℝ) (hk : 1 < k) :
    AmplifierRealized k ∧ KrausWellDefined (amplifierKraus k) ∧
    (∀ a : ℝ, 1 ≤ a → ThermalRealized a ∧ ThermalRealized (k ^ 2 * a + k ^ 2 - 1) ∧
      TraceHasSum (fun ell => krausTerm (amplifierKraus k ell) (thermalDensity a))
        (thermalDensity (k ^ 2 * a + k ^ 2 - 1))) ∧
    (∀ n : ℕ, HasFockMatrix (amplifierDyadOutput k n n) (amplifierDyadMatrix k n n) ∧
      IsDensity (amplifierDyadOutput k n n) ∧
      TraceHasSum (fun ell => krausTerm (amplifierKraus k ell) (fockDyad n n))
        (amplifierDyadOutput k n n) ∧
      TraceHasSum (fun ell =>
        ((Nat.choose (n + ell) ell : ℝ) * (1 - (k⁻¹) ^ 2) ^ ell *
          (k⁻¹) ^ (2 * n + 2) : ℂ) • fockDyad (n + ell) (n + ell))
        (amplifierDyadOutput k n n)) ∧
    (∀ lambda : ℝ, 0 ≤ lambda → PoissonRealized lambda ∧
      HasFockMatrix (amplifierPoissonOutput k lambda) (amplifierPoissonMatrix k lambda) ∧
      TraceHasSum (fun ell => krausTerm (amplifierKraus k ell) (poissonDensity lambda))
        (amplifierPoissonOutput k lambda) ∧ SuperPoissonian (amplifierPoissonOutput k lambda)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
