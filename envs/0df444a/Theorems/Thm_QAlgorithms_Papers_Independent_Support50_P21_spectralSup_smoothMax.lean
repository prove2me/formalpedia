-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_spectralSup_smoothMax
-- name    : QAlgorithms.Papers.Independent.Support50.P21.spectralSup_smoothMax
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:53:31.902244+00:00
-- url     : https://prove2.me/theorems/61edc590-35da-465e-980a-dd51273474ec
-- title:
--   Theorem 2 (§VIII.A): smooth max-relative entropy gives spectral sup-divergence
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Fix a nonzero finite-dimensional system $H$. Let $\rho_n$ be density operators and $\sigma_n\ge0$ on $H^{\otimes n}$ for each $n\ge1$. Define $\Pi_n(\gamma)=\rho_n-2^{n\gamma}\sigma_n$ and
--
--   $$\overline D(\hat\rho\Vert\hat\sigma)=\inf\{\gamma\in\mathbb R:\limsup_{n\to\infty}\operatorname{Tr}[\{\Pi_n(\gamma)\ge0\}\Pi_n(\gamma)]=0\}.$$
--
--   Then, in the extended real topology,
--
--   $$\overline D(\hat\rho\Vert\hat\sigma)=\lim_{\varepsilon\downarrow0}\limsup_{n\to\infty}\frac1nD_{\max}^{\varepsilon}(\rho_n\Vert\sigma_n).$$
--
--   The limit in $n$ is taken first. There are no iid, support, trace-bound-on-$\sigma_n$, or finite-rate assumptions. This identifies the spectral sup-divergence rate with the smoothed asymptotic quantity.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 8, Theorem 2 (§VIII.A): smooth max-relative entropy gives spectral sup-divergence

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

/-- Theorem 2, PDF pp.8–9, (53): arbitrary (not necessarily iid) tensor-register
sequences; n=k+1. No support, trace-bound-on-sigma, or finite-rate hypothesis. -/
theorem spectralSup_smoothMax (rho sigma : (k : ℕ) → Mat (PositiveTensorBasis I k))
    (hrho : ∀ k, IsDensityMatrix (rho k)) (hsigma : ∀ k, (sigma k).PosSemidef) :
    Tendsto (maxAsymptotic rho sigma) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (spectralSup rho sigma)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
