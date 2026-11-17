-- Prove2me | Theorems.Thm_RankingCertGap_Supplement_theorem_7
-- name    : RankingCertGap.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:59:54.322996+00:00
-- url     : https://prove2.me/theorems/79bf28ff-cf6b-4c19-897b-53b76e26bf5e
-- title:
--   Theorem 7 — exact two-regular values, gap, unique optimizer, and Stieltjes measure
-- statement:
--   On nonempty two-regular bipartite instances,
--   $$
--   \widetilde\Gamma(2)=\frac34,qquad
--   \widetilde\gamma(2)=\frac{119}{144},qquad
--   \widetilde\Delta(2)=\frac{11}{144}.
--   $$
--   The unique optimizer over $\mathcal F$ equals $3/4$ on $[0,1)$ and $1$ at $1$, and its Stieltjes measure is
--   $$
--   \pi_{\widetilde f^\star_2}=\frac34\delta_0+\frac14\delta_1.
--   $$
--
--   This identifies the entire two-regular certifying gap and shows that it is not caused by a suboptimal monotone profile.
--
--   **Formalization Note** The theorem is over $\mathcal F$; the published goal separately establishes the same capacity over the larger class $\mathcal A$.
--
--   Differences from the source:
--   - encoding: profiles and Stieltjes measures on $[0,1]$ → total real profiles and probability measures on $\mathbb R$ identified by lower-interval values on $[0,1]$; reason: this matches the published profile representation without changing source values
--   - encoding: unique optimizer on $[0,1]$ → equality at every point of $[0,1]$; reason: values outside the source domain are irrelevant
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Theorem 7, p.10, eqs. (26)–(27)

import Mathlib
import Definitions.Def_RankingCertGap_Supplement_Objects

set_option autoImplicit false

open MeasureTheory

namespace RankingCertGap.Supplement

/-- **Theorem 7 (Two-regular graphs: exact values and gap).** Xu, arXiv:2610.17545 (held file
sha256 75896dd9…), Theorem 7, p.10, eqs. (26)–(27). The capacity, competitiveness and gap are
exact, `fTilde` is the unique optimizer over `𝒽`, and its Stieltjes measure is the printed two-atom
probability measure.

**Formalization Note.** This theorem is over `classF`; the published Proposition 2 separately gives
the same capacity over the larger class `classA`. Optimizer equality is pointwise on `[0,1]`. -/
theorem theorem_7 :
    GammaC classF (regular 2) = 3 / 4 ∧
    gammaC (regular 2) = 119 / 144 ∧
    gapC classF (regular 2) = 11 / 144 ∧
    fTilde ∈ classF ∧
    chiC fTilde (regular 2) = GammaC classF (regular 2) ∧
    (∀ f : ℝ → ℝ, f ∈ classF →
      chiC f (regular 2) = GammaC classF (regular 2) →
      ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = fTilde y) ∧
    HasStieltjesMeasure fTilde
      (ENNReal.ofReal (3 / 4) • Measure.dirac (0 : ℝ) +
        ENNReal.ofReal (1 / 4) • Measure.dirac (1 : ℝ)) := by sorry

end RankingCertGap.Supplement
