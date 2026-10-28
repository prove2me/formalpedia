-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_smoothMax_strict_tail
-- name    : QAlgorithms.Papers.Independent.Support50.P21.smoothMax_strict_tail
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:49:55.998092+00:00
-- url     : https://prove2.me/theorems/572465a1-c271-4c7e-bbe7-8b8f0d70c151
-- title:
--   Lemma 15
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho,\sigma$ be density operators and $\lambda\in\mathbb R$. Set
--
--   $$\varepsilon=\sqrt{8\operatorname{Tr}[\{\rho>2^\lambda\sigma\}\rho]}.$$
--
--   Then $D_{\max}^{\varepsilon}(\rho\Vert\sigma)\le\lambda$, using the full trace-norm, trace-capped smoothing ball. The projector is strict and the trace is against $\rho$; a zero tail permits $\varepsilon=0$. This bounds smoothing by a spectral tail.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 7, Lemma 15

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

/-- Lemma 15, PDF p.7; proof p.11: STRICT spectral tail of rho, not positive-part trace. -/
theorem smoothMax_strict_tail (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (lambda : ℝ) :
    traceSmoothMax (Real.sqrt (8 * tr (strictPositive
      (rho - (((2 : ℝ) ^ lambda) : ℂ) • sigma) * rho))) rho sigma ≤
      (lambda : EReal) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
