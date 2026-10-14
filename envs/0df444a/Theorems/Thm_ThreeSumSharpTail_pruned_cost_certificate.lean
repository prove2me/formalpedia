-- Prove2me | Theorems.Thm_ThreeSumSharpTail_pruned_cost_certificate
-- name    : ThreeSumSharpTail.pruned_cost_certificate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:53:33.377607+00:00
-- url     : https://prove2.me/theorems/e5befbc8-a6d9-4a15-b637-3d5c6b6ddddf
-- title:
--   Sharp-tail certificate bounds the exact pruned preprocessing and query costs
-- statement:
--   Let c>10 be an integer, theta in (0,9/10), and a>0,s rational. Under a(A(c)+Gamma(c,theta))<1, s<Gamma(c,theta), and s<1/2-q(theta), there exist C>=0 and a threshold m0 such that for every D>=2 with D<=N^a and m=ceil(log_4 D)>=m0 the tile fits, cost8p<=C N^2 (log D)^2/D^s, and costQuery<=C D^(1/2-s) log D. The quantities are the existing pruned program cost functions, with the exact binomial tail retained.
-- source:
--   Derived interface transfer for Xu, same manuscript, Sections 3-4. Uses the existing complete CorollaryP.costs proof in ThreeSumApsp/Pruned/Costs.lean at commit 27a2fa4bab32 and the proved pruned encoding comparison. Actual finite program correctness and reductions remain separate obligations.

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_ThreeSumSharpTail_pruned_encoding_comparison
set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSumApsp
open ThreeSumSharpTail

theorem ThreeSumSharpTail.pruned_cost_certificate (c : ℕ) (θ : ℝ) (a s : ℚ)
    (hc : 10 < c) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (ha0 : 0 < a)
    (henc : (a : ℝ) * (encodingExponent c + sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - queryExponent θ) :
    ∃ C m₀, 0 ≤ C ∧ ∀ D₀ N m : ℕ,
      2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf (c : ℝ) m) m ≤ N ∧
      cost8p (levelsOf (c : ℝ) m) m (switchOf θ m) N ≤
        C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ (s : ℝ)) ∧
      costQuery (levelsOf (c : ℝ) m) m (switchOf θ m) ≤
        C * ((D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) * Real.log (D₀ : ℝ)) := by sorry
