-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_theorem_4_7
-- name    : SingleSampleCombPI.XOS.Supplement.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:57.039892+00:00
-- url     : https://prove2.me/theorems/c7f68dc1-88cb-4ef8-aefc-ef12582b0e8a
-- title:
--   Theorem 4.7 — Exact one-minus-one-over-e Algorithm 6 under adversarial arrivals
-- statement:
--   For normalized nonnegative monotone twice-differentiable DR-submodular concave valuations on the nonnegative orthant, Algorithm 6 makes well-defined choices satisfying its implicit Condition 1 at every arrival. For every fixed buyer arrival order it satisfies
--   $$\mathrm{FD}(\mathrm{Alg}_6(v))\ge(1-e^{-1})\mathrm{Opt}(v).$$
--   The canonical Aumann–Shapley supporting map is used throughout. No polynomial-time or arbitrary-support-oracle version is asserted.
--
--   Differences from the source:
--   - encoding: twice-differentiable DR-submodular concave valuations on the nonnegative orthant and Algorithm 6 → within-orthant first/second Frechet derivatives, antitone gradient, canonical Aumann–Shapley prices and reachable frozen-history transitions; reason: these are Definition 6 and Proposition 2.2 conventions; C² regularity, Lipschitz constants and arbitrary supplied supporting maps are not assumed
--   - encoding: valid states, traces and arbitrary arrival order → inductively reachable histories and explicit order-indexed frozen records; reason: only initialization and actual Condition 1 transitions are assumed; no lemma conclusion or unproved algorithmic invariant is a state field
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 4.7, printed p. 20 / PDF p. 22; proof printed 24–27 / PDF 26–29.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_GreedyDR

namespace SingleSampleCombPI.XOS.Supplement

/-- Theorem 4.7, PDF 22 / printed 20. The exact Algorithm 6 has
well-defined choices and its guarantee holds for every fixed arrival order. -/
theorem theorem_4_7 {n m : ℕ} (v : Fin n → Vec m → ℝ)
    (hv : ∀ i, DRConcave (v i)) (ρ : Equiv.Perm (Fin n)) :
    (∀ i, condition1 (savedState (alg6 n m) () ρ (fun j => drBuyer (v j)) i)
      (v i) ((alg6 n m).step
        (savedState (alg6 n m) () ρ (fun j => drBuyer (v j)) i) i (drBuyer (v i))).1) ∧
    gamma * Opt .divisible (fun i => drBuyer (v i)) ≤
      FD .divisible (fun i => drBuyer (v i))
        (fdRun (alg6 n m) () ρ (fun i => drBuyer (v i))) := by sorry

end SingleSampleCombPI.XOS.Supplement
