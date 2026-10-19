-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_attenuatorExplicitKraus
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.attenuatorExplicitKraus
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:30:40.267737+00:00
-- url     : https://prove2.me/theorems/f85a2f3a-4dca-4a81-b2ab-b83f605f3385
-- title:
--   Eq.(4.6),(4.11): attenuator Kraus and Fock-dyad action
-- statement:
--   Let $0<\kappa<1$. The displayed $B_\ell(\kappa)$ family is a complete family of actual bounded operators on the full Fock space. Its exact Fock-dyad action is
--
--   $$C_{1,\kappa}(|m\rangle\langle n|)=\sum_{\ell=0}^{\min(m,n)}\sqrt{\binom m\ell\binom n\ell}(1-\kappa^2)^\ell\kappa^{m+n-2\ell}|m-\ell\rangle\langle n-\ell|.$$
--
--   The Kraus map is defined by trace-norm summation on every trace-class input and has strong normalization. With $\chi_\rho(z)=\operatorname{tr}[D(z)\rho]$ for the source's actual Weyl displacement, it is the attenuator channel:
--
--   $$\chi_{C_{1,\kappa}(\rho)}(z)=\chi_\rho(\kappa z)\exp[-(1-\kappa^2)|z|^2/2].$$
--
--   The dyad formula includes zero photon indices.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 14, Eq.(4.6),(4.11): attenuator Kraus and Fock-dyad action

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Eqs.(4.6),(4.11), PDF pp.14–15: complete bounded attenuator family,
its exact finite Fock-fockDyad law, and the source characteristic identification. -/
theorem attenuatorExplicitKraus (k : ℝ) (hk : 0 < k) (hku : k < 1) :
    DisplacementRealized ∧ AttenuatorRealized k ∧ KrausWellDefined (attenuatorKraus k) ∧
    (∀ m n : ℕ, TraceHasSum
      (fun ell => krausTerm (attenuatorKraus k ell) (fockDyad m n))
      (attenuatorDyadOutput k m n)) ∧
    (∀ X : FockOperator, IsDensity X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (attenuatorKraus k ell) X) Y ∧ IsDensity Y ∧
      ∀ z : ℂ, characteristic Y z = characteristic X ((k : ℂ) * z) *
        (Real.exp (-(1 - k ^ 2) * Complex.normSq z / 2) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
