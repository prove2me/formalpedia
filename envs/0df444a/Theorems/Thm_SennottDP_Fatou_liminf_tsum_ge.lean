-- Prove2me | Theorems.Thm_SennottDP_Fatou_liminf_tsum_ge
-- name    : SennottDP.Fatou.liminf_tsum_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T11:42:34.834795+00:00
-- url     : https://prove2.me/theorems/5dc05de0-00d8-4051-8ea6-7aae7e94fe60
-- title:
--   Proposition A.1.7 — Fatou's inequality for countable sums of nonnegative terms
-- statement:
--   Let $S$ be a countable set and, for each $j\in S$, let $(u(j,N))_N$ be a sequence with values in $[0,\infty]$. Then
--   $$\liminf_{N\to\infty}\ \sum_{j\in S} u(j,N) \;\ge\; \sum_{j\in S}\ \liminf_{N\to\infty} u(j,N). \tag{A.3}$$
--
--   This is Fatou's lemma for counting measure on a countable set; it generalizes Proposition A.1.5 to countably many nonnegative terms.
--
--   **Formalization Note** All values and sums are in `ℝ≥0∞`, where every series of nonnegative terms has a value. The statement is an instance of Mathlib's `MeasureTheory.lintegral_liminf_le` for the counting measure; it is kept as a named step of the book's chain of results.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 273, Proposition A.1.7, Eq. (A.3)

import Mathlib

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Proposition A.1.7, p. 273, (A.3). `S` is countable and `u(j, N) ∈ [0, ∞]`:
`liminf_N ∑_{j ∈ S} u(j, N) ≥ ∑_{j ∈ S} liminf_N u(j, N)`. -/
theorem liminf_tsum_ge {S : Type*} [Countable S] (u : S → ℕ → ℝ≥0∞) :
    ∑' j, liminf (fun N => u j N) atTop ≤ liminf (fun N => ∑' j, u j N) atTop := by sorry

end SennottDP.Fatou
