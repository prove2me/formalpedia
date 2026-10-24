-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_spectralInf_smoothMin
-- name    : QAlgorithms.Papers.Independent.Support50.P21.spectralInf_smoothMin
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:54:06.89399+00:00
-- url     : https://prove2.me/theorems/6619c060-7ba3-4526-ab23-8a42ba0b3a12
-- title:
--   Theorem 3 (§VIII.B): smooth min-relative entropy gives spectral inf-divergence
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Fix a nonzero finite-dimensional system $H$. Let $\rho_n$ be density operators and $\sigma_n\ge0$ on $H^{\otimes n}$ for $n\ge1$. Define $\Pi_n(\gamma)=\rho_n-2^{n\gamma}\sigma_n$ and
--
--   $$\underline D(\hat\rho\Vert\hat\sigma)=\sup\{\gamma\in\mathbb R:\liminf_{n\to\infty}\operatorname{Tr}[\{\Pi_n(\gamma)\ge0\}\Pi_n(\gamma)]=1\}.$$
--
--   Then, in the extended real topology,
--
--   $$\underline D(\hat\rho\Vert\hat\sigma)=\lim_{\varepsilon\downarrow0}\liminf_{n\to\infty}\frac1nD_{\min}^{\varepsilon}(\rho_n\Vert\sigma_n).$$
--
--   The order of limits is as displayed, with no iid, support, trace-bound-on-$\sigma_n$, or finite-rate assumptions. This identifies the spectral inf-divergence rate with the smoothed asymptotic quantity.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 9, Theorem 3 (§VIII.B): smooth min-relative entropy gives spectral inf-divergence

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- Theorem 3, PDF pp.9–10, (67): first n→infinity, then eps→0+.
Proof (78) requires arbitrarily small slack at liminf, not a new hypothesis. -/
theorem spectralInf_smoothMin (rho sigma : (k : ℕ) → Mat (PositiveTensorBasis I k))
    (hrho : ∀ k, IsDensityMatrix (rho k)) (hsigma : ∀ k, (sigma k).PosSemidef) :
    Tendsto (minAsymptotic rho sigma) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (spectralInf rho sigma)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
