-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_lemma2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.lemma2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:52:06.745295+00:00
-- url     : https://prove2.me/theorems/d17610e5-6d83-43bd-ac5f-e5600c3873a3
-- title:
--   Lemma 2 (printed “LemmaS 2”): restrictions to a dense increasing union
-- statement:
--   Let $H,H'$ be separable complex Hilbert spaces, $k\ge1$, and $\Phi:\mathcal T(H)\to\mathcal T(H')$ a channel. Let $H_n$ be increasing closed Hilbert subspaces of $H$ with
--
--   $$\overline{\bigcup_n H_n}=H.$$
--
--   If the restriction of $\Phi$ to density inputs supported on $H_n$ is $k$-partially entanglement breaking for every $n$, then $\Phi$ is $k$-partially entanglement breaking. Each restricted condition includes every separable ancillary system and every density state on $H_n$ tensored with that ancilla.
--
--   No finite-dimensionality assumption on the subspaces is imposed.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 11, Lemma 2 (printed “LemmaS 2”): restrictions to a dense increasing union

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF p.11, Lemma 2 (printed LemmaS 2).
Closed subspaces form an increasing dense union. They need not have finite dimension. -/
theorem lemma2 {I J : Type} [Countable I] [Countable J]
    (k : ℕ) (hk : 0 < k) (Phi : CanonicalChannel I J) (S : ℕ → Submodule ℂ (Hilbert I))
    (hclosed : ∀ n, IsClosed (S n : Set (Hilbert I))) (hmono : Monotone S)
    (hdense : closure (⋃ n, (S n : Set (Hilbert I))) = Set.univ)
    (hrestr : ∀ n, restrictionPEB k Phi (S n)) : isPEB k Phi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
