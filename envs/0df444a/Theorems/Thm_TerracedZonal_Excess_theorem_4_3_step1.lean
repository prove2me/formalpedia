-- Prove2me | Theorems.Thm_TerracedZonal_Excess_theorem_4_3_step1
-- name    : TerracedZonal.Excess.theorem_4_3_step1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:42.439212+00:00
-- url     : https://prove2.me/theorems/c4681a18-85b1-43dd-87e0-195389952dc3
-- title:
--   Step 1 (proof of Theorem 4.3) — Stage 1 is a near-minimizer of $G_{c_{\mathrm{step}}}$
-- statement:
--   Let $m_N$ be a Stage-1 output of TerracedZonal for every sufficiently large $N$ (any exact window minimizer of $G_{c_{\mathrm{step}}}$ followed by any run of the repair loop to $\sum_k m_k=N-2$). Then there is a function $g(N)=o(N^{2/3})$ such that, for all large $N$,
--
--   $$G_{c_{\mathrm{step}}}(m_N)\le\min G_{c_{\mathrm{step}}}+g(N),$$
--
--   where $\min G_{c_{\mathrm{step}}}$ is the minimum of Lemma E.5 over all integer vectors with $m_k\ge1$. In words: the mass repair costs only $o(N^{2/3})$ on top of the exact unconstrained optimum.
--
--   Differences from the source:
--   - generalization: min G_{c_step} (the dynamic program minimizes over the window) → the minimum of Lemma E.5 over all vectors with m_k ≥ 1; reason: the all-vector minimum is no larger than the window minimum, so this inequality implies the printed window-minimum inequality for every source output; Stage 1 itself still minimizes over the window
--   - generalization: the output of the reference implementation (Viterbi arg min and a least-cost repair move, tie-breaks unspecified) → every exact minimizer of G_{c_step} over the window and every admissible least-cost repair choice; reason: the paper fixes no tie-break; the reference implementation is one such choice, so the statement for every choice specializes to it
--   - generalization: the Stage-1 output for every N ≥ 3 → any family m_N that is a Stage-1 output for all sufficiently large N; reason: the conclusion is asymptotic in N; a family that is a Stage-1 output for every N ≥ 3 is in particular eventually one
--   - reading: endpoint peel: the first ring of a terrace of length ≥ 2 changes by sgn(diff) → the peel is allowed only when the peeled ring keeps population ≥ 1; reason: the Ensure line of Algorithm 1a requires every m_k ≥ 1; the paper does not state the guard at the peel; with the guard the loop never stalled in an exhaustive check of all repair choices for 3 ≤ N < 2000 and 150 random N < 2·10⁵
--   - encoding: round(·) with no stated half-integer convention (K, y_k^base, w) → Mathlib's round, half-integers rounded up; reason: the paper fixes no convention; Mathlib round is the standard half-up rounding, and one fixed convention is needed to define the algorithm
--   - reading: K = round((π − 2θ_cap)/h₀) in Algorithm 1a line 1, K = max(1, round(…)) in eq. (18) → K = max(1, round((π − 2θ_cap)/h₀)); reason: the two printed versions differ only when the round is 0 (e.g. N = 3); eq. (18) is the definition and yields at least one ring
--   - encoding: ∑_k m_k = N − 2 → ∑_k m_k + 2 = N in ℕ; reason: avoids truncated subtraction; identical for N ≥ 2
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), proof of Theorem 4.3, Step 1, p. 30 (PDF 31)

import Definitions.Def_TerracedZonal_Excess_Stage1

namespace TerracedZonal.Excess

open Filter

/-- Proof of Theorem 4.3, Step 1, p. 30 (PDF 31): Stage 1 is a near-minimizer. For every family
of Stage-1 outputs `m_N` (eventually in `N`), `G_{c_step}(m_N) ≤ min G_{c_step} + o(N^{2/3})`,
the minimum being that of Lemma E.5 (all `m_k ≥ 1`). -/
theorem theorem_4_3_step1 (m : ∀ N : ℕ, Pops N)
    (hm : ∀ᶠ N : ℕ in atTop, IsStage1Output N (m N)) :
    ∃ g : ℕ → ℝ, g =o[atTop] (fun N : ℕ => (N : ℝ) ^ (2 / 3 : ℝ)) ∧
      ∀ᶠ N : ℕ in atTop, Gcost cStep N (m N) ≤ minG cStep N + g N := by sorry

end TerracedZonal.Excess
