-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_collision_le_max
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.collision_le_max
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:36:33.635869+00:00
-- url     : https://prove2.me/theorems/1fc7249b-2f07-4f8b-ad56-7147bd2114b9
-- title:
--   Collision relative entropy is bounded by max-relative entropy
-- statement:
--   Let $\rho,\sigma\ge0$ act on a nonzero finite-dimensional complex Hilbert space, with $\operatorname{Tr}\rho\le1$. Use the unnormalized Petz collision divergence $S_2(\rho\Vert\sigma)=\log_2\operatorname{Tr}(\rho^2\sigma^{-1})$ on containing supports and $D_{\max}(\rho\Vert\sigma)=\inf\{\lambda\in\mathbb R:\rho\le2^\lambda\sigma\}$. Then
--
--   $$S_2(\rho\Vert\sigma)\le D_{\max}(\rho\Vert\sigma).$$
--
--   The inverse acts on the spectral support. Unsupported nonzero $\rho$ has value $+\infty$ and $\rho=0$ has value $-\infty$ on both sides. Neither $\rho$ nor $\sigma$ is required to have trace one. This compares collision and max-relative entropic controls.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 5, Lemma 7, collision relative entropy versus max-relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

/-- Lemma 7, PDF pp.5–6. Petz order two has no trace normalization;
rho=0 gives -infinity, unsupported nonzero rho gives +infinity. -/
theorem collision_le_max {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (htrace : rho.trace.re ≤ 1) : petzD 2 rho sigma ≤ maxRelative rho sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
