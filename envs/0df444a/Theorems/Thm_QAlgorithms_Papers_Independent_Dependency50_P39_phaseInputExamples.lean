-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_phaseInputExamples
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.phaseInputExamples
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:28:03.60618+00:00
-- url     : https://prove2.me/theorems/f6c3b08e-c06b-4b7a-90ac-71dd23c30b51
-- title:
--   Eqs.(3.36)–(3.39): Fock and Poissonian inputs
-- statement:
--   Let $\kappa>0$. The phase-conjugator output on a Fock input is
--
--   $$D_\kappa(|n\rangle\langle n|)=\sum_{j\ge0}\binom{n+j}{j}\frac{\kappa^{2j}}{(1+\kappa^2)^{n+j+1}}|j\rangle\langle j|.$$
--
--   Every density output has strictly positive Fock diagonal entries. Consequently a density with a zero diagonal entry cannot be fixed. For a Poissonian input $\rho_\lambda=e^{-\lambda}\sum_{j\ge0}(\lambda^j/j!)|j\rangle\langle j|$, $\lambda\ge0$, the output diagonal weight at $n$ is
--
--   $$\frac{e^{-\lambda}}{1+\kappa^2}\sum_{j\ge0}\frac{\lambda^j}{j!}\binom{n+j}{j}(1+\kappa^2)^{-j}(1+\kappa^{-2})^{-n}.$$
--
--   All defining scalar series and trace-class Kraus sums converge. The output has finite first and second photon-number moments and variance strictly greater than its mean. This includes the vacuum Poisson input $\lambda=0$.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 12, Eqs.(3.36)–(3.39): Fock and Poissonian inputs

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Eq.(3.37)–(3.39), PDF pp.11–12: exact Fock and Poisson input laws,
strict output diagonal positivity, non-invariance when a diagonal is zero,
and genuinely super-Poissonian output statistics for k>0. -/
theorem phaseInputExamples (k : ℝ) (hk : 0 < k) :
    KrausWellDefined (phaseKraus k) ∧
    (∀ n : ℕ, HasFockMatrix (phaseFockOutput k n) (phaseFockMatrix k n) ∧
      IsDensity (phaseFockOutput k n) ∧
      TraceHasSum (fun ell => krausTerm (phaseKraus k ell) (fockDyad n n))
        (phaseFockOutput k n)) ∧
    (∀ X : FockOperator, IsDensity X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (phaseKraus k ell) X) Y ∧ IsDensity Y ∧
      ∀ n : ℕ, 0 < photonProbability Y n) ∧
    (∀ X : FockOperator, IsDensity X → (∃ n : ℕ, X (fockKet n) n = 0) →
      ¬ TraceHasSum (fun ell => krausTerm (phaseKraus k ell) X) X) ∧
    (∀ lambda : ℝ, 0 ≤ lambda → PoissonRealized lambda ∧
      (∀ n : ℕ, Summable (fun j : ℕ => phasePoissonTerm k lambda n j)) ∧
      HasFockMatrix (phasePoissonOutput k lambda) (phasePoissonMatrix k lambda) ∧
      TraceHasSum (fun ell => krausTerm (phaseKraus k ell) (poissonDensity lambda))
        (phasePoissonOutput k lambda) ∧ SuperPoissonian (phasePoissonOutput k lambda)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
