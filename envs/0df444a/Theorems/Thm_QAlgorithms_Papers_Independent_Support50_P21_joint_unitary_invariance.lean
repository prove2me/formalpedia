-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_joint_unitary_invariance
-- name    : QAlgorithms.Papers.Independent.Support50.P21.joint_unitary_invariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:46:38.664994+00:00
-- url     : https://prove2.me/theorems/0cc54f2e-9b32-483d-bbd3-9150effa8b3b
-- title:
--   Lemma 11
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho\ge0$ with $\operatorname{Tr}\rho\le1$, let $\sigma\ge0$, and let $U$ be unitary. Then
--
--   $$D_{\min}(U\rho U^\dagger\Vert U\sigma U^\dagger)=D_{\min}(\rho\Vert\sigma),$$
--   $$D_{\max}(U\rho U^\dagger\Vert U\sigma U^\dagger)=D_{\max}(\rho\Vert\sigma).$$
--
--   The same unitary acts on both arguments. Singular and zero operators use the extended definitions, so no invertibility assumption is added.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 5, Lemma 11

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

/-- Lemma 11, PDF p.5: joint unitary invariance, including singular inputs. -/
theorem joint_unitary_invariance (rho sigma : Mat I)
    (hrho : IsSubnormalized rho) (hsigma : sigma.PosSemidef)
    (U : Matrix.unitaryGroup I ℂ) :
    dMin (conjSuperop (U : Mat I) rho) (conjSuperop (U : Mat I) sigma) = dMin rho sigma ∧
    maxRelative (conjSuperop (U : Mat I) rho) (conjSuperop (U : Mat I) sigma) = maxRelative rho sigma := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
