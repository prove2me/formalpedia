-- Prove2me | Theorems.Thm_ThreeSumSharpTail_rational_cost_regime
-- name    : ThreeSumSharpTail.rational_cost_regime
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T18:21:55.924989+00:00
-- url     : https://prove2.me/theorems/3edaf29a-0559-4471-b17a-a4f9bc203272
-- title:
--   Finite rational parameters realizing the sharp-tail cost regime
-- statement:
--   For integer c>10 and rational eta,a,s satisfying the strict encoding, preprocessing and query inequalities, with 0<a<1 and 0<s<1/2, there are a finite rational parameter record G and a uniform constant C>=0 such that CostsWithinP holds for every 1<=D<=N^a. The preprocessing bound is N^2(log D+1)^2/D^s and the query bound is D^(1/2-s)(log D+1). The record represents c exactly and eta by its integer numerator and denominator, and includes a fixed threshold for the bounded-size cases.
-- source:
--   Derived finite-parameter interface for Xu, same manuscript, Sections 3-4. It consumes the proved pruned cost certificate and the actual RatParams/CostsWithinP definitions of the published pruned program.

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_ThreeSumSharpTail_pruned_cost_certificate
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open ThreeSumApsp Light.Sec4

theorem ThreeSumSharpTail.rational_cost_regime
    (c : ℕ) (η a s : ℚ) (hc : 10 < c)
    (hη0 : 0 < η) (hη9 : η < 9 / 10)
    (ha0 : 0 < a) (ha1 : (a : ℝ) < 1)
    (hs0 : 0 < s) (hs5 : (s : ℝ) < 1 / 2)
    (henc : (a : ℝ) * (ThreeSumSharpTail.encodingExponent c +
      ThreeSumSharpTail.sharpSaving c (η : ℝ)) < 1)
    (hprep : (s : ℝ) < ThreeSumSharpTail.sharpSaving c (η : ℝ))
    (hquery : (s : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent (η : ℝ)) :
    ∃ G : Light.Sec4.RatParams, ∃ C : ℝ, 0 ≤ C ∧
      ∀ N D₀ : ℕ, 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
        Light.Sec4.CostsWithinP G C N D₀
          ((N : ℝ) ^ 2 * (Real.log (D₀ : ℝ) + 1) ^ 2 / (D₀ : ℝ) ^ (s : ℝ))
          ((D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log (D₀ : ℝ) + 1)) := by sorry
