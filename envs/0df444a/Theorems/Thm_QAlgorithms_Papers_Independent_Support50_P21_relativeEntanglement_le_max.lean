-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_relativeEntanglement_le_max
-- name    : QAlgorithms.Papers.Independent.Support50.P21.relativeEntanglement_le_max
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:48:18.033046+00:00
-- url     : https://prove2.me/theorems/3d068b5f-8b4b-4e59-9b09-8452df30436f
-- title:
--   Lemma 13
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho_{AB}$ be a bipartite density operator, and let $\mathcal D$ contain all separable density operators on the same space. With minima over that entire set,
--
--   $$E(\rho):=\min_{\sigma\in\mathcal D}S(\rho\Vert\sigma)\le\min_{\sigma\in\mathcal D}D_{\max}(\rho\Vert\sigma)=E_{\max}(\rho).$$
--
--   The relative-entropy minimum is attained. This is the upper-bound clause advertised in the abstract; neither optimization is restricted to product states.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 7, Lemma 13

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

/-- Lemma 13, PDF p.7, (38)–(39): all separable comparison states.
The unsubscripted D in the first line of (38) is the surrounding Dmax. -/
theorem relativeEntanglement_le_max (rho : Mat (I × J)) (hrho : IsDensityMatrix rho) :
    eRelative rho ≤ eMax rho ∧
    ∃ sigma : Mat (I × J), IsSeparableDensity sigma ∧ unnormalizedRelativeBits rho sigma = eRelative rho := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
