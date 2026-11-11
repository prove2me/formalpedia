-- Prove2me | Theorems.Thm_TerracedZonal_Excess_appendix_C2_repair_terminates
-- name    : TerracedZonal.Excess.appendix_C2_repair_terminates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:30.288675+00:00
-- url     : https://prove2.me/theorems/945f6c81-d565-48b7-b5fa-27440dc65cff
-- title:
--   App. C.2 — Stage 1 is well defined: a window minimizer exists and the repair loop terminates
-- statement:
--   Let $N\ge3$. Then:
--
--   1. $G_{c_{\mathrm{step}}}$ has a minimizer over the window (4);
--   2. every iteration of the repair loop strictly decreases $|\mathrm{diff}|$, where $\mathrm{diff}=(N-2)-\sum_k m_k$; hence a run from $m^{(0)}$ has at most $|\mathrm{diff}_0|$ iterations;
--   3. along every run of the loop started at a window minimizer, as long as $\mathrm{diff}\ne0$ an iteration is possible (an admissible seam-free move or, failing that, an endpoint peel);
--   4. consequently, from every window minimizer the loop reaches a vector with
--
--   $$\sum_{k=0}^{K-1}m_k=N-2.$$
--
--   So Stage-1 outputs exist for every $N\ge3$, and the hypotheses of Theorem 4.3 can be met.
--
--   Differences from the source:
--   - generalization: the output of the reference implementation (Viterbi arg min and a least-cost repair move, tie-breaks unspecified) → every exact minimizer of G_{c_step} over the window and every admissible least-cost repair choice; reason: the paper fixes no tie-break; the reference implementation is one such choice, so the statement for every choice specializes to it
--   - reading: endpoint peel: the first ring of a terrace of length ≥ 2 changes by sgn(diff) → the peel is allowed only when the peeled ring keeps population ≥ 1; reason: the Ensure line of Algorithm 1a requires every m_k ≥ 1; the paper does not state the guard at the peel; with the guard the loop never stalled in an exhaustive check of all repair choices for 3 ≤ N < 2000 and 150 random N < 2·10⁵
--   - encoding: the loop terminates after at most |diff₀| iterations → every iteration strictly decreases |diff|; reason: a strictly decreasing sequence of natural numbers starting at |diff₀| has at most |diff₀| steps
--   - encoding: round(·) with no stated half-integer convention (K, y_k^base, w) → Mathlib's round, half-integers rounded up; reason: the paper fixes no convention; Mathlib round is the standard half-up rounding, and one fixed convention is needed to define the algorithm
--   - reading: K = round((π − 2θ_cap)/h₀) in Algorithm 1a line 1, K = max(1, round(…)) in eq. (18) → K = max(1, round((π − 2θ_cap)/h₀)); reason: the two printed versions differ only when the round is 0 (e.g. N = 3); eq. (18) is the definition and yields at least one ring
--   - encoding: ∑_k m_k = N − 2 → ∑_k m_k + 2 = N in ℕ; reason: avoids truncated subtraction; identical for N ≥ 2
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), App. C.2, p. 21 (PDF 22)

import Definitions.Def_TerracedZonal_Excess_Stage1

namespace TerracedZonal.Excess

/-- App. C.2, p. 21 (PDF 22): for every `N ≥ 3` a window minimizer exists; every repair move
strictly decreases `|diff|` (so at most `|diff₀|` iterations occur); along every run of the
loop from a minimizer an admissible move exists while `diff ≠ 0`; hence the loop ends with
`∑_k m_k = N - 2`. -/
theorem appendix_C2_repair_terminates (N : ℕ) (hN : 3 ≤ N) :
    (∃ m₀ : Pops N, IsPreRepair N m₀) ∧
    (∀ m m' : Pops N, RepairStep N m m' → |residual N m'| < |residual N m|) ∧
    (∀ m₀ : Pops N, IsPreRepair N m₀ → ∀ m : Pops N, Relation.ReflTransGen (RepairStep N) m₀ m →
      residual N m ≠ 0 → ∃ m' : Pops N, RepairStep N m m') ∧
    (∀ m₀ : Pops N, IsPreRepair N m₀ → ∃ m : Pops N,
      Relation.ReflTransGen (RepairStep N) m₀ m ∧ ∑ k, m k + 2 = N) := by sorry

end TerracedZonal.Excess
