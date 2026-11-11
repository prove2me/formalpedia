-- Prove2me | Theorems.Thm_TerracedZonal_Excess_theorem_4_3_step3_core
-- name    : TerracedZonal.Excess.theorem_4_3_step3_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:46.950046+00:00
-- url     : https://prove2.me/theorems/d11f41e2-5f17-4a20-920e-9e72b613375b
-- title:
--   Step 3 (proof of Theorem 4.3) — unconditional core: $G_{c_{\mathrm{seam}}}(m)=C_1N^{2/3}+o(N^{2/3})$
-- statement:
--   Let $m_N$ be a Stage-1 output for every sufficiently large $N$. Then
--
--   $$G_{c_{\mathrm{seam}}}(m_N)=G_{c_{\mathrm{step}}}(m_N)-(c_{\mathrm{step}}-c_{\mathrm{seam}})S(m_N)=C_1N^{2/3}+o(N^{2/3}),\qquad C_1=\frac13\Big(1+\frac{2c_{\mathrm{seam}}}{c_{\mathrm{step}}}\Big)C(c_{\mathrm{step}}).$$
--
--   The Lean statement asserts the outer equality, $G_{c_{\mathrm{seam}}}(m_N)-C_1N^{2/3}=o(N^{2/3})$; the first equality is an identity of the definitions. This is the part of Step 3 that does not use locality (A): it concerns the one-dimensional cost Stage 1 builds, with seams re-priced at $c_{\mathrm{seam}}$. With (A) it gives Theorem 4.3 at once.
--
--   Differences from the source:
--   - reading: Step 3: E(X_N) − E_BHS(N) = G_{c_seam}(m) + o(N^{2/3}) [by (A)] = G_{c_step}(m) − (c_step − c_seam)S(m) + o(N^{2/3}) = C₁N^{2/3} + o(N^{2/3}) → G_{c_seam}(m_N) − C₁N^{2/3} = o(N^{2/3}), without the first equality; reason: the first equality is locality (A), a hypothesis of Theorem 4.3; this milestone is the remainder of the chain, which holds without (A), and the title marks it as the unconditional core
--   - generalization: the output of the reference implementation (Viterbi arg min and a least-cost repair move, tie-breaks unspecified) → every exact minimizer of G_{c_step} over the window and every admissible least-cost repair choice; reason: the paper fixes no tie-break; the reference implementation is one such choice, so the statement for every choice specializes to it
--   - generalization: the Stage-1 output for every N ≥ 3 → any family m_N that is a Stage-1 output for all sufficiently large N; reason: the conclusion is asymptotic in N; a family that is a Stage-1 output for every N ≥ 3 is in particular eventually one
--   - reading: endpoint peel: the first ring of a terrace of length ≥ 2 changes by sgn(diff) → the peel is allowed only when the peeled ring keeps population ≥ 1; reason: the Ensure line of Algorithm 1a requires every m_k ≥ 1; the paper does not state the guard at the peel; with the guard the loop never stalled in an exhaustive check of all repair choices for 3 ≤ N < 2000 and 150 random N < 2·10⁵
--   - encoding: round(·) with no stated half-integer convention (K, y_k^base, w) → Mathlib's round, half-integers rounded up; reason: the paper fixes no convention; Mathlib round is the standard half-up rounding, and one fixed convention is needed to define the algorithm
--   - reading: K = round((π − 2θ_cap)/h₀) in Algorithm 1a line 1, K = max(1, round(…)) in eq. (18) → K = max(1, round((π − 2θ_cap)/h₀)); reason: the two printed versions differ only when the round is 0 (e.g. N = 3); eq. (18) is the definition and yields at least one ring
--   - encoding: ∑_k m_k = N − 2 → ∑_k m_k + 2 = N in ℕ; reason: avoids truncated subtraction; identical for N ≥ 2
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), proof of Theorem 4.3, Step 3, p. 30 (PDF 31)

import Definitions.Def_TerracedZonal_Excess_Stage1

namespace TerracedZonal.Excess

open Filter

/-- Proof of Theorem 4.3, Step 3, p. 30 (PDF 31), the part not using locality (A): for every
family of Stage-1 outputs `m_N`, `G_{c_seam}(m_N) = C₁ N^{2/3} + o(N^{2/3})`. -/
theorem theorem_4_3_step3_core (m : ∀ N : ℕ, Pops N)
    (hm : ∀ᶠ N : ℕ in atTop, IsStage1Output N (m N)) :
    (fun N : ℕ => Gcost cSeam N (m N) - C1 * (N : ℝ) ^ (2 / 3 : ℝ)) =o[atTop]
      (fun N : ℕ => (N : ℝ) ^ (2 / 3 : ℝ)) := by sorry

end TerracedZonal.Excess
