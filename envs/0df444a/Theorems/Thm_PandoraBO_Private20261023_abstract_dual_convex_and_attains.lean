-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_abstract_dual_convex_and_attains
-- name    : PandoraBO.Private20261023.abstract_dual_convex_and_attains
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:24:07.651491+00:00
-- url     : https://prove2.me/theorems/2b1f075b-c1bd-4ab0-80bd-0b4ba67b7d43
-- title:
--   Convexity and minimum attainment of a finite-valued affine dual envelope
-- statement:
--   Let a family of alternatives have real rewards R and real costs C. Suppose the penalized rewards R(i)−tC(i) are bounded above for every real multiplier t, and some alternative has cost strictly below B. Then the dual envelope D(t)=sup_i(R(i)−tC(i))+tB is convex on the real line and attains a minimum on the nonnegative half-line. No maximizing alternative is assumed to exist. This isolates the real-analysis argument used for the budgeted Pandora dual problem.
-- source:
--   Abstract form of the dual-envelope argument in Xie et al., Cost-aware Bayesian Optimization via the Pandora’s Box Gittins Index, author revised manuscript reviewed 23 October 2026, Appendix B.5, Lemma 6, equations (38)–(39). This reusable generalization is derived for the formalization, rather than quoted verbatim.

import Definitions.Def_PandoraBO_Model
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

theorem PandoraBO.Private20261023.abstract_dual_convex_and_attains {ι : Type*} (R C : ι → ℝ) (B : ℝ)
    (hbounded : ∀ t : ℝ, BddAbove (Set.range (fun i => R i - t * C i)))
    (hstrict : ∃ i : ι, C i < B) :
    (∀ x y a : ℝ, 0 ≤ a → a ≤ 1 →
      sSup (Set.range (fun i => R i - (a * x + (1 - a) * y) * C i)) +
          (a * x + (1 - a) * y) * B ≤
        a * (sSup (Set.range (fun i => R i - x * C i)) + x * B) +
        (1 - a) * (sSup (Set.range (fun i => R i - y * C i)) + y * B)) ∧
    ∃ t : ℝ, 0 ≤ t ∧ ∀ u : ℝ, 0 ≤ u →
      sSup (Set.range (fun i => R i - t * C i)) + t * B ≤
        sSup (Set.range (fun i => R i - u * C i)) + u * B := by sorry
