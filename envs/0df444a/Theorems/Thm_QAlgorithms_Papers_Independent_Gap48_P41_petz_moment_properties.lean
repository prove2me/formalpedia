-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_petz_moment_properties
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.petz_moment_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:29:21.123535+00:00
-- url     : https://prove2.me/theorems/adf1e660-eb01-4d90-a603-158395b76b21
-- title:
--   Convex Petz moment, entropy slope and compact maximizers
-- statement:
--   Let $I$ be a nonempty finite orthonormal basis, and let $\rho,\sigma$ be positive semidefinite complex matrices of trace one with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. For a positive integer $n$, an arbitrary effect $0\le A_n\le I$ accepts the null state $\rho^{\otimes n}$. Write $\alpha_n(A_n)=\operatorname{Tr}[\rho^{\otimes n}(I-A_n)]$ and $\beta_n(A_n)=\operatorname{Tr}[\sigma^{\otimes n}A_n]$. All logarithms are natural, with $\log0=-\infty$ in rates. Write $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$, using support-restricted spectral logarithms inside the trace.
--
--   Put $\psi(s)=\log\operatorname{Tr}(\rho^{1+s}\sigma^{-s})$ and $\phi(\lambda)=\max_{0\le s\le1}\{\lambda s-\psi(s)\}$. Spectral powers vanish on the kernel, including at zero and negative orders.
--
--   The function $\psi$ is convex on $[0,1]$, $\psi(0)=0$, and $\psi'(0)=D(\rho\Vert\sigma)$. Moreover,
--   $$
--   \lambda>D(\rho\Vert\sigma)\ \Longrightarrow\ \phi(\lambda)>0.
--   $$
--   For $D(\rho\Vert\sigma)\le\lambda\le\psi'(1)$ and $s\in[0,1]$,
--   $$
--   s\in\operatorname*{argmax}_{0\le t\le1}\{\lambda t-\psi(t)\}
--   \quad\Longleftrightarrow\quad\psi'(s)=\lambda.
--   $$
--   These properties identify the entropy threshold and the compact optimizer condition, without claiming uniqueness.
--
--   **Formalization Note** Endpoint derivatives use the finite spectral expression on a neighborhood of the interval. The displayed strict second-derivative claim on page 3 is corrected to nonnegative curvature, as required by the equal-state case.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 3, §2, unnumbered properties and (9): convex moment, slope, positive transform

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P41

open scoped Matrix ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (tr SupportLE relativeEntropy scalarPower classicalD typeI accept TestSequence
    scaled logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Claimed50.P15 (legendre)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

/-- PDF pp.3--4, unnumbered properties and (9): convexity, slope, positivity,
and membership in the set of maximizers. SOURCE CORRECTION: the displayed
psi''>0 on p.3 must be psi''>=0; identical states give psi=0. The prose convexity
claim is retained without an invented nondegeneracy or unique-maximizer premise. -/
theorem petz_moment_properties [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) :
    ConvexOn ℝ (Set.Icc 0 1) (petzPsi rho sigma) ∧
    petzPsi rho sigma 0 = 0 ∧
    HasDerivAt (petzPsi rho sigma) (relativeEntropy rho sigma).toReal 0 ∧
    (∀ lambda : ℝ, (relativeEntropy rho sigma).toReal < lambda →
      0 < petzPhi rho sigma lambda) ∧
    (∀ lambda : ℝ, (relativeEntropy rho sigma).toReal ≤ lambda →
      lambda ≤ deriv (petzPsi rho sigma) 1 → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (IsGreatest ((fun t : ℝ => lambda * t - petzPsi rho sigma t) '' Set.Icc 0 1)
        (lambda * s - petzPsi rho sigma s) ↔ deriv (petzPsi rho sigma) s = lambda)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
