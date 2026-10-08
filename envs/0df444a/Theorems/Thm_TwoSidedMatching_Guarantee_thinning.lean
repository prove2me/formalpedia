-- Prove2me | Theorems.Thm_TwoSidedMatching_Guarantee_thinning
-- name    : TwoSidedMatching.Guarantee.thinning
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:12.946374+00:00
-- url     : https://prove2.me/theorems/45550105-a9a5-4342-8893-25aa8ea6d9f9
-- title:
--   Supplemental Note p. 12 — request counts are Poisson
-- statement:
--   For each t in [0,T], the numbers Nᵈₜ and Nˢₜ of myopic buyer and seller requests have Poisson laws with parameters λᵈt F̄ᵈ(p*) and λˢt Fˢ(w*). By the balancing equations, both parameters equal μ*t/T:
--
--   $$\lambda^dt\bar F^d(p^*)=\lambda^stF^s(w^*)=\mu^*t/T.$$
--
--   These are the two request streams used in the policy analysis.
--
--   **Formalization Note** Measurability of each count map is included so the mapped measures have their intended values.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note p. 12, proof of Theorem 2 (PDF p. 52)

import Mathlib
import Definitions.Def_TwoSidedMatching_Guarantee_Market

open MeasureTheory

namespace TwoSidedMatching.Guarantee

/-- Supplemental Note p. 12: accepted arrivals on each side are Poisson
with rate μ*/T, up to any time in the horizon. -/
theorem thinning (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS ≤ E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun ω : Ω => Nd E lamD lamS T ω t) ∧
      Measurable (fun ω : Ω => Ns E lamD lamS T ω t) ∧
      Measure.map (fun ω : Ω => Nd E lamD lamS T ω t) (P E lamD lamS T) =
        ProbabilityTheory.poissonMeasure
          ⟨max (lamD * t * FdBar E (pStar E lamD lamS T)) 0, le_max_right _ _⟩ ∧
      Measure.map (fun ω : Ω => Ns E lamD lamS T ω t) (P E lamD lamS T) =
        ProbabilityTheory.poissonMeasure
          ⟨max (lamS * t * Fs E (wStar E lamD lamS T)) 0, le_max_right _ _⟩ ∧
      lamD * t * FdBar E (pStar E lamD lamS T) = muStar E lamD lamS T * t / T ∧
      lamS * t * Fs E (wStar E lamD lamS T) = muStar E lamD lamS T * t / T := by sorry

end TwoSidedMatching.Guarantee
