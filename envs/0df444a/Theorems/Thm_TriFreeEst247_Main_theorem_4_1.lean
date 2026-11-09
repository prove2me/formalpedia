-- Prove2me | Theorems.Thm_TriFreeEst247_Main_theorem_4_1
-- name    : TriFreeEst247.Main.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:01:03.278628+00:00
-- url     : https://prove2.me/theorems/1af27aae-66a8-4356-b0ca-f66cf4586891
-- title:
--   Theorem 4.1: BHHS subsampling for dense 3-CSPs
-- statement:
--   There are absolute constants $c,C>0$ such that for every dense normalized 3-CSP $Q$ on $n$ variables with finite alphabet $A$, every $0<\theta<1$, and every integer $N$ satisfying
--
--   $$\max\{3,c\theta^{-C}\log|A|\}\le N\le n,$$
--
--   a uniformly random $N$-element subset $U$ satisfies
--
--   $$|\mathbb E_U\mathrm{OPT}_{\mathrm{CSP}}(Q;U)-\mathrm{OPT}_{\mathrm{CSP}}(Q)|\le\theta.$$
--
--   The sampled optimum uses the full-instance normalization and inherited local functions. This imported subsampling result controls the absolute difference, including both directions.
--
--   Differences from the source:
--   - encoding: finite CSP variable sets and alphabets → Fin n vertices, finite alphabet types, and attained finite real suprema; reason: bijections and finite nonempty maxima preserve all instances
--   - reading: absolute constants and log |A| in the sampling threshold → positive real c,C before A,n,Q,θ,N and the natural logarithm; reason: the polynomial and O constants are absolute and quantified before every varying parameter
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.15, Theorem 4.1

import Mathlib
import Definitions.Def_TriFreeEst247_Main_DenseCSP

open scoped ENNReal

namespace TriFreeEst247.Main

theorem theorem_4_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (A : Type) [Fintype A] (n : ℕ)
      (Q : CSP n A), isDense Q → ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∀ N : ℕ, 3 ≤ N → c * θ ^ (-C) * Real.log (Fintype.card A : ℝ) ≤ (N : ℝ) →
        N ≤ n → |expectedSampledOpt Q N - cspOpt Q| ≤ θ := by sorry

end TriFreeEst247.Main
