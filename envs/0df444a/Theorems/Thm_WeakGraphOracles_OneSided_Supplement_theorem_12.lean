-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_theorem_12
-- name    : WeakGraphOracles.OneSided.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:31:35.280195+00:00
-- url     : https://prove2.me/theorems/a02bbff2-6dea-444d-90b3-7f6a1d267971
-- title:
--   Theorem 12 — interval-concentrated targets: $P_\alpha^+$ is GEN3 testable with $O(k^2\log k/\epsilon^4)$ queries
-- statement:
--   For a sorted target vector $\alpha\in[0,n-1]^n$ let $P_\alpha^+$ be the set of $n$-vertex graphs $G$ whose sorted degree vector satisfies $\mathrm{hist}(G)\ge\alpha$ coordinatewise. Farness is measured by $\mathrm{dist}_\oplus$. In GEN3 the tester knows $n$ and $|E(G)|$ and may make random-neighbour, random-edge and degree queries.
--
--   There is a universal constant $C>0$ such that the following holds. Let $\epsilon\in(0,1]$, let $\delta,\gamma\ge0$ with $\delta+2\gamma\le\epsilon/4$, and let $\alpha$ be $(\delta,\gamma,k)$-interval concentrated (Definition 7). Then there is a GEN3 tester for $P_\alpha^+$ with respect to $\mathrm{dist}_\oplus$, accepting every member and rejecting every $\epsilon$-far graph with probability at least $2/3$, that makes at most
--
--   $$C\,\frac{k^2\log(k+2)}{\epsilon^4}$$
--
--   queries; the bound depends neither on $n$ nor on $\alpha$ nor on the lengths of the intervals.
--
--   The theorem shows that upward-closed degree-vector targets concentrated on a constant number of essentially constant blocks are testable once $|E(G)|$ is known; Lemma 6.4 shows that some concentration assumption is needed.
--
--   Differences from the source:
--   - encoding: O(k² log k/ε⁴) queries → q ≤ C·k²·log(k+2)/ε⁴ with a universal C > 0; reason: log k vanishes at k = 1, where the tester still needs queries; log(k+2) is within a constant factor of log k for k ≥ 2 and gives the usual nonzero convention at k = 1 (the proof's sample size is ⌈32k² log(6k)/(9ε⁴)⌉)
--   - encoding: |E(G)| as part of the input in GEN3 (the canonical tester starts by querying it) → a family of GEN2 policies indexed by the public edge count, the one for |E(G)| being run; reason: GEN3 as defined in §1 and §3; not charging the edge-count request changes the count by the constant 1
--   - reading: δ, γ (concentration tolerances) → 0 ≤ δ and 0 ≤ γ; reason: tolerances are nonnegative in Definition 7's reading 'do not differ by more than a (1 − γ) fraction'; a negative γ with a large δ is not an instance of the source
--   - encoding: index intervals [a_h, b_h] ⊆ [n] → 0-based indices a_h ≤ b_h in Fin n; reason: a shift of indexing
--   - encoding: G is ε-far from P: its dist⊕ distance to the closest graph of P is at least ε → ε ≤ dist⊕(G, G') for every G' ∈ P on the same labels; reason: same condition (finitely many graphs, the minimum is attained); an empty P makes every graph far, the +∞ convention
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 14 (PDF p. 15), Theorem 12, with Definition 7 on the same page; proof §7.9, pp. 23–25 (PDF pp. 24–26)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_degrees

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Theorem 12, printed p. 14 (PDF p. 15). There is a universal `C > 0` such that
for every `ε ∈ (0,1]`, nonnegative `δ, γ` with `δ + 2γ ≤ ε/4`, every `k`, every
`n` and every sorted target `α ∈ [0,n-1]^n` that is `(δ,γ,k)`-interval
concentrated (Definition 7), `P_α^+ = {G : hist(G) ≥ α}` is two-sided error
testable in GEN3 (with `|E(G)|` public) with respect to `dist⊕`, with
`q ≤ C k² log(k+2) / ε⁴` queries — the source's `O(k² log k / ε⁴)`, with
`log(k+2)` keeping the bound nonzero at `k = 1`. -/
theorem theorem_12 :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε δ γ : ℝ) (k n : ℕ) (α : Fin n → ℕ),
      0 < ε → ε ≤ 1 → 0 ≤ δ → 0 ≤ γ → δ + 2 * γ ≤ ε / 4 →
      IsDegreeTarget α → IntervalConcentrated δ γ k α →
      ∃ q : ℕ, (q : ℝ) ≤ C * (k : ℝ) ^ 2 * Real.log ((k : ℝ) + 2) / ε ^ 4 ∧
        ∃ A : ℕ → GEN2Policy n q,
          GEN3TwoSidedCorrect (fun G => DominatesTarget α G)
            (DistFar (fun G' => DominatesTarget α G') ε) A := by sorry

end WeakGraphOracles.OneSided.Supplement
