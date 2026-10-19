-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_amplifierExplicitKraus
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.amplifierExplicitKraus
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:34:29.706994+00:00
-- url     : https://prove2.me/theorems/7227d6fc-092f-4c3a-8d08-44e7017847ca
-- title:
--   Eq.(5.5),(5.13): amplifier Kraus and Fock-dyad action
-- statement:
--   Let $\kappa>1$. The displayed $A_\ell(\kappa)$ family consists of bounded operators on the full oscillator space, is strongly complete, and has trace-norm-convergent output on every trace-class input. For all $n,m\in\mathbb N$,
--
--   $$C_{2,\kappa}(|n\rangle\langle m|)=\kappa^{-(n+m+2)}\sum_{\ell\ge0}(1-\kappa^{-2})^\ell
--   \frac{\sqrt{(n+\ell)!(m+\ell)!}}{\ell!\sqrt{n!m!}}|n+\ell\rangle\langle m+\ell|.$$
--
--   The displayed output series and the original Kraus series converge in trace norm to the same actual bounded trace-class operator. The $\kappa^{-1}$ prefactor in each Kraus operator and $\kappa^{-2}$ in each diagonal output are retained.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 19, Eq.(5.5),(5.13): amplifier Kraus and Fock-dyad action

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Eqs.(5.5),(5.13), PDF pp.19–20: complete bounded amplifier family and
its trace-norm Fock-fockDyad expansion, including the k^-2 output normalization. -/
theorem amplifierExplicitKraus (k : ℝ) (hk : 1 < k) :
    AmplifierRealized k ∧ KrausWellDefined (amplifierKraus k) ∧
    ∀ n m : ℕ, HasFockMatrix (amplifierDyadOutput k n m) (amplifierDyadMatrix k n m) ∧
      TraceHasSum (fun ell => amplifierDyadCoefficient k n m ell •
        fockDyad (n + ell) (m + ell)) (amplifierDyadOutput k n m) ∧
      TraceHasSum (fun ell => krausTerm (amplifierKraus k ell) (fockDyad n m))
        (amplifierDyadOutput k n m) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
