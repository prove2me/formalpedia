-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_maxRelative_entanglement_monotone
-- name    : QAlgorithms.Papers.Independent.Support50.P21.maxRelative_entanglement_monotone
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:38:07.087539+00:00
-- url     : https://prove2.me/theorems/bfcdb1f0-0db0-4496-a6be-95cb24fd615e
-- title:
--   Theorem 1 (§V): max-relative entropy of entanglement is an entanglement monotone
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho_{AB}$ be a bipartite density operator, and let $\mathcal D$ be the set of all separable density operators on the same space. The minimum
--
--   $$E_{\max}(\rho)=\min_{\sigma\in\mathcal D}D_{\max}(\rho\Vert\sigma)$$
--
--   is attained and finite. It is nonnegative, vanishes exactly on separable states, and is invariant under local unitaries. For every finite adaptive LOCC instrument producing normalized conditional states $\rho_i$ with probabilities $p_i$,
--
--   $$\sum_i p_i E_{\max}(\rho_i)\le E_{\max}(\rho).$$
--
--   The statement includes every one-step local instrument and allows local dimension changes, outcome-dependent continuations, and discarded transcripts. This makes $E_{\max}$ an entanglement monotone.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 6, Theorem 1 (§V): max-relative entropy of entanglement is an entanglement monotone

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

/-- Theorem 1, PDF p.6, (35), with the definition of monotone on pp.6,12.
The false proof identity (36), which uses a sum instead of a maximum for
orthogonal blocks, is not assumed. Minimum attainment and finiteness are explicit. -/
theorem maxRelative_entanglement_monotone :
    (∀ rho : Mat (I × J), IsDensityMatrix rho →
      ∃ z : ℝ, 0 ≤ z ∧ eMax rho = (z : EReal) ∧
        ∃ sigma : Mat (I × J), IsSeparableDensity sigma ∧ maxRelative rho sigma = eMax rho) ∧
    (∀ rho : Mat (I × J), IsDensityMatrix rho →
      (eMax rho = 0 ↔ IsSeparableDensity rho)) ∧
    (∀ (rho : Mat (I × J)), IsDensityMatrix rho →
      ∀ (U : Matrix.unitaryGroup I ℂ) (V : Matrix.unitaryGroup J ℂ),
      eMax (conjSuperop (Matrix.kronecker (U : Mat I) (V : Mat J)) rho) = eMax rho) ∧
    IsAverageLocalMonotone bundledEMax ∧ IsAdaptiveLOCCMonotone bundledEMax := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
