-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_interruptedAmplification
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.interruptedAmplification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:39:16.267371+00:00
-- url     : https://prove2.me/theorems/9313f123-c235-4f69-b7b6-10ad44f800ef
-- title:
--   Interrupted amplification: exact gain and Zeno limit
-- statement:
--   Fix integers $N\ge1$ and $0\le\ell\le N$. Apply $\ell$ amplifier segments of squeeze duration $2/N$, resetting the ancilla to vacuum after each. Their complete Kraus map has gain
--
--   $$\kappa_{N,\ell}=\cosh(2/N)^\ell,\qquad
--   1\le\kappa_{N,\ell}\le\cosh(2\ell/N).$$
--
--   The zero-segment map is the identity. At total duration $2$, $\cosh(2/N)^N\to1$. For each fixed integer $\ell\ge0$, the leading correction printed in the source is expressed precisely as
--
--   $$\lim_{N\to\infty}N^2\bigl(\cosh(2/N)^\ell-1\bigr)=2\ell.$$
--
--   Map equality holds for every trace-class input with trace-norm convergence. This is the interrupted vacuum-dilation construction, not a separate Lindblad-semigroup claim.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 24, Interrupted amplification: exact gain and Zeno limit

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF pp.23–24: exact interrupted amplification and its Zeno gain limit.
The total squeezing duration is 2, and each step uses a fresh vacuum ancilla. -/
theorem interruptedAmplification :
    (∀ N : ℕ, 1 ≤ N → ∀ ell : ℕ, ell ≤ N →
      AmplifierRealized (Real.cosh (2 / (N : ℝ))) ∧
      AmplifierRealized (Real.cosh (2 / (N : ℝ)) ^ ell) ∧
      KrausEquivalent (iteratedKraus (amplifierKraus (Real.cosh (2 / (N : ℝ)))) ell)
        (amplifierKraus (Real.cosh (2 / (N : ℝ)) ^ ell)) ∧
      1 ≤ Real.cosh (2 / (N : ℝ)) ^ ell ∧
      Real.cosh (2 / (N : ℝ)) ^ ell ≤ Real.cosh (2 * (ell : ℝ) / (N : ℝ))) ∧
    Tendsto (fun N : ℕ => Real.cosh (2 / (N : ℝ)) ^ N) atTop (nhds 1) ∧
    (∀ ell : ℕ, Tendsto
      (fun N : ℕ => (N : ℝ) ^ 2 * (Real.cosh (2 / (N : ℝ)) ^ ell - 1))
      atTop (nhds (2 * (ell : ℝ)))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
