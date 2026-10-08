-- Prove2me | Theorems.Thm_TwoSidedMatching_Guarantee_lemma_2
-- name    : TwoSidedMatching.Guarantee.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:20:17.213658+00:00
-- url     : https://prove2.me/theorems/59a5d99f-dfee-4f7c-b8f1-7a8cf95d3fd2
-- title:
--   Lemma 2 — clairvoyant value is below the fluid value
-- statement:
--   In the regular two-sided market with nonnegative waiting costs, the clairvoyant matching value has a finite expectation, and
--
--   $$\mathbb E[\bar J(H^T)]\le\bar J^*.$$
--
--   It makes the deterministic optimum a stochastic-policy benchmark.
--
--   **Formalization Note** Integrability is concluded rather than assumed. Nonnegative support endpoints align the fluid feasible prices with the paper's price domain.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text p. 17, Lemma 2 (PDF p. 18)

import Mathlib
import Definitions.Def_TwoSidedMatching_Guarantee_Market

open MeasureTheory

namespace TwoSidedMatching.Guarantee

/-- Main text Lemma 2: the deterministic program bounds expected clairvoyant
virtual surplus, with its expectation explicitly finite. -/
theorem lemma_2 (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS ≤ E.hiB)
    (hloB : 0 ≤ E.loB) (hloS : 0 ≤ E.loS)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h) :
    Integrable (Jbar E b h) (P E lamD lamS T) ∧
      (∫ ω, Jbar E b h ω ∂P E lamD lamS T) ≤ fluidValue E lamD lamS T := by sorry

end TwoSidedMatching.Guarantee
