-- Prove2me | Theorems.Thm_RockafellarMaxMono_Maximality_minty_maximal_monotone
-- name    : RockafellarMaxMono.Maximality.minty_maximal_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:05:51.503275+00:00
-- url     : https://prove2.me/theorems/740f2cc4-d59c-4a16-88db-a087bbc003f7
-- title:
--   §3, p. 213 — Minty's theorem: finite continuous convex functions have maximal monotone subdifferentials
-- statement:
--   Let $V$ be a real Banach space with dual $V^*$, and let $h : V \to \mathbb{R}$ be a convex function that is finite and continuous everywhere on $V$. Then its subdifferential
--
--   $$
--   \partial h : V \to V^*
--   $$
--
--   is a maximal monotone operator.
--
--   This is the case of Theorem A established earlier by Minty, which Rockafellar quotes and applies to the function $(f+j)^*$ on the Banach space $E^*$; it is therefore stated for an arbitrary real Banach space $V$ rather than only for $E$.
--
--   **Formalization Note** "Everywhere finite" is real-valuedness of $h$; convexity is Mathlib's `ConvexOn ℝ Set.univ h`; continuity is for the norm topology. The subdifferential is taken of $h$ viewed as a function into $(-\infty,+\infty]$.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 213, §3, Proof of Theorem A (citing Minty [2])

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Maximality_MonotoneOperator

namespace RockafellarMaxMono.Maximality

theorem minty_maximal_monotone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h) :
    IsMaximalMonotone (Shared.subdiff (fun x => ((h x : ℝ) : EReal))) := by sorry

end RockafellarMaxMono.Maximality
