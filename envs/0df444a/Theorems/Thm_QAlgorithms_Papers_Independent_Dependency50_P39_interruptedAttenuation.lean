-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_interruptedAttenuation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.interruptedAttenuation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:33:54.278018+00:00
-- url     : https://prove2.me/theorems/f00cec2c-4527-464b-b59c-58856e7a3c58
-- title:
--   Interrupted attenuation: exact parameter and suppression
-- statement:
--   Fix integers $N\ge1$ and $0\le\ell\le N$. Repeat $\ell$ attenuator segments of angle $\pi/(2N)$, with a fresh vacuum ancilla after each segment. The complete product-indexed Kraus map is
--
--   $$C_1\!\left(\cos\!\left(\frac{\pi}{2N}\right)^\ell\right).$$
--
--   Its parameter lies between the uninterrupted parameter $\cos(\ell\pi/(2N))$ and $1$. At fixed total angle $\pi/2$,
--
--   $$\lim_{N\to\infty}\cos\!\left(\frac{\pi}{2N}\right)^N=1.$$
--
--   The zero-segment case is the identity; $N=1$ includes total attenuation. Equality of maps is stated on every trace-class input with trace-norm convergence. The erroneous printed large-$N$ coefficient is separately deferred.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 18, Interrupted attenuation: exact parameter and suppression

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF pp.17–18: interrupted attenuation with a reset ancilla at each segment.
The exact cosine power is used; the erroneous printed asymptotic coefficient
is not asserted. N=1 and ell=0 retain their endpoint interpretations. -/
theorem interruptedAttenuation :
    (∀ N : ℕ, 1 ≤ N → ∀ ell : ℕ, ell ≤ N →
      AttenuatorRealized (Real.cos (Real.pi / (2 * (N : ℝ)))) ∧
      AttenuatorRealized (Real.cos (Real.pi / (2 * (N : ℝ))) ^ ell) ∧
      KrausEquivalent
        (iteratedKraus (attenuatorKraus (Real.cos (Real.pi / (2 * (N : ℝ))))) ell)
        (attenuatorKraus (Real.cos (Real.pi / (2 * (N : ℝ))) ^ ell)) ∧
      Real.cos ((ell : ℝ) * Real.pi / (2 * (N : ℝ))) ≤
        Real.cos (Real.pi / (2 * (N : ℝ))) ^ ell ∧
      Real.cos (Real.pi / (2 * (N : ℝ))) ^ ell ≤ 1) ∧
    Tendsto (fun N : ℕ => Real.cos (Real.pi / (2 * (N : ℝ))) ^ N)
      atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
