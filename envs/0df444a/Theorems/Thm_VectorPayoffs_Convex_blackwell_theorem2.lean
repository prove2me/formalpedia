-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_blackwell_theorem2
-- name    : VectorPayoffs.Convex.blackwell_theorem2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:07:08.206611+00:00
-- url     : https://prove2.me/theorems/164c80e4-fda3-453a-abda-cc188665b8ef
-- title:
--   THEOREM 2 — a bounded sequence with conditional drift ≤ −u E|z_k| crosses level t with probability ≤ ((1−u)/(1+u))^t
-- statement:
--   Let $z_1,z_2,\dots$ be real random variables on a probability space with $|z_k|\le1$ almost surely, and let $0<u<1$. Suppose that for every $k\ge1$, almost surely,
--   $$E(z_k\mid z_1,\dots,z_{k-1})\le -u\,E(|z_k|\mid z_1,\dots,z_{k-1}).$$
--   Then for every real $t$,
--   $$\mathrm{Prob}\{z_1+\dots+z_k\ge t\text{ for some }k\ge1\}\le\Big(\frac{1-u}{1+u}\Big)^t .$$
--
--   This is the form of the strong law of large numbers that Blackwell quotes from his earlier paper and applies, in the proof of the LEMMA, to the rescaled increments of the approach process.
--
--   **Formalization Note** The page prints "$-u\max(|z_k|\mid z_1,\dots,z_{k-1})$" on the right of the hypothesis. The cited source (Blackwell 1954) and the proof use the conditional expectation $E(|z_k|\mid\cdot)$; since this is at most any conditional maximum, the hypothesis stated here is the weaker one and the theorem the stronger one, and the paper's derivation of (8) delivers it. The bound $u<1$ is added: for $u\ge1$ the base $(1-u)/(1+u)$ is $\le0$ and has no real $t$-th power (Lean's `rpow` would return a junk value). $|z_k|\le1$ is required almost surely. The $z_k$ are measurable, and $t$ is an arbitrary real (the bound is $\ge1$ for $t\le0$).
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, p. 5, THEOREM 2 (quoted from Blackwell, On optimal systems, Ann. Math. Statist. 25, 1954)

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Recursion

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §2, p. 5, THEOREM 2 (conditional expectation form of the drift
hypothesis; see the natural-language statement for the printed "max"). -/
theorem blackwell_theorem2 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (z : ℕ → Ω → ℝ) (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hmeas : ∀ k, 1 ≤ k → Measurable (z k))
    (hbound : ∀ k, 1 ≤ k → ∀ᵐ ω ∂μ, |z k ω| ≤ 1)
    (hdrift : ∀ k, 1 ≤ k →
      μ[z k | pastSigma z (k - 1)] ≤ᵐ[μ] (-u) • μ[fun ω => |z k ω| | pastSigma z (k - 1)])
    (t : ℝ) :
    μ {ω | ∃ k, 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.Icc 1 k, z i ω} ≤
      ENNReal.ofReal (((1 - u) / (1 + u)) ^ t) := by sorry

end VectorPayoffs.Convex
