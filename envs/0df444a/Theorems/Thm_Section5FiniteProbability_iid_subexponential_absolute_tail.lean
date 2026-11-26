-- Prove2me | Theorems.Thm_Section5FiniteProbability_iid_subexponential_absolute_tail
-- name    : Section5FiniteProbability.iid_subexponential_absolute_tail
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T11:52:35.417781+00:00
-- url     : https://prove2.me/theorems/d4da78b5-3408-5eb7-afb9-7f3c673809c5
-- title:
--   Finite Bernstein bound for independent weighted samples
-- statement:
--   Let p be nonnegative weights on a finite outcome space and Y a real statistic. Assume that for every real l with |l| times 512 at most 1/2, its weighted exponential moment is at most exp(8388608 l squared). For any finite set of independent sample positions J and t nonnegative, the product-weight mass of outcomes with absolute summed statistic at least |J|t is at most
--
--   $$2\exp(-|J|\min(t^2,t)/33554432).$$
--
--   This auxiliary concentration result supports the Section 5 tomography analysis; it does not establish the quantum measurement compiler.
-- source:
--   Original auxiliary result for https://arxiv.org/html/2609.40331v3, Section 5; Solutions/Section5FiniteBatchMGF.lean

import Mathlib
variable {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]

theorem Section5FiniteProbability.iid_subexponential_absolute_tail (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (Y : Ω → ℝ)
    (hmgf : ∀ l : ℝ, |l| *512 ≤ 1/2 →
      (∑ x, p x*Real.exp (l*Y x)) ≤ Real.exp (8388608*l^2))
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ x : J → Ω, if (Fintype.card J : ℝ)*t ≤ |∑ r, Y (x r)| then ∏ r, p (x r) else 0) ≤
      2*Real.exp (-(Fintype.card J : ℝ)*min (t^2) t/33554432) := by sorry
