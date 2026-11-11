-- Prove2me | Theorems.Thm_TerracedZonal_Excess_theorem_4_3_step2
-- name    : TerracedZonal.Excess.theorem_4_3_step2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:40.944198+00:00
-- url     : https://prove2.me/theorems/7fcb991a-533f-4c4a-b2ca-dbaf379eea60
-- title:
--   Step 2 (proof of Theorem 4.3) — seams carry two thirds of the Stage-1 cost
-- statement:
--   Let $\lambda_0=c_{\mathrm{step}}$ and let $m_N$ be a Stage-1 output for every sufficiently large $N$. Then
--
--   $$S(m_N)=C'(\lambda_0)\,N^{2/3}(1+o(1)),\qquad C'(\lambda_0)=\frac23\,\frac{C(\lambda_0)}{\lambda_0},$$
--
--   and the seam part $\lambda_0S(m_N)$ of $G_{\lambda_0}(m_N)$ is two thirds of the total:
--
--   $$\lim_{N\to\infty}\frac{\lambda_0\,S(m_N)}{G_{\lambda_0}(m_N)}=\frac23.$$
--
--   Here $S(m)=\sum_{k\ge1,\,m_k\ne m_{k-1}}\tfrac12(y_{k-1}+y_k)$ is the seam weight. This is what allows re-pricing the seams at $c_{\mathrm{seam}}$ in Step 3.
--
--   Differences from the source:
--   - encoding: S(m) = C′(λ₀)N^{2/3}(1 + o(1)); "λ₀S(m) is two thirds of its total" → IsEquivalent of S(m_N) and C′(λ₀)N^{2/3}; λ₀S(m_N)/G_{λ₀}(m_N) → 2/3; reason: C′(λ₀) > 0, so equivalence is ratio → 1; "two thirds of the total" is read asymptotically, as the derivation gives it
--   - generalization: the output of the reference implementation (Viterbi arg min and a least-cost repair move, tie-breaks unspecified) → every exact minimizer of G_{c_step} over the window and every admissible least-cost repair choice; reason: the paper fixes no tie-break; the reference implementation is one such choice, so the statement for every choice specializes to it
--   - generalization: the Stage-1 output for every N ≥ 3 → any family m_N that is a Stage-1 output for all sufficiently large N; reason: the conclusion is asymptotic in N; a family that is a Stage-1 output for every N ≥ 3 is in particular eventually one
--   - reading: endpoint peel: the first ring of a terrace of length ≥ 2 changes by sgn(diff) → the peel is allowed only when the peeled ring keeps population ≥ 1; reason: the Ensure line of Algorithm 1a requires every m_k ≥ 1; the paper does not state the guard at the peel; with the guard the loop never stalled in an exhaustive check of all repair choices for 3 ≤ N < 2000 and 150 random N < 2·10⁵
--   - encoding: round(·) with no stated half-integer convention (K, y_k^base, w) → Mathlib's round, half-integers rounded up; reason: the paper fixes no convention; Mathlib round is the standard half-up rounding, and one fixed convention is needed to define the algorithm
--   - reading: K = round((π − 2θ_cap)/h₀) in Algorithm 1a line 1, K = max(1, round(…)) in eq. (18) → K = max(1, round((π − 2θ_cap)/h₀)); reason: the two printed versions differ only when the round is 0 (e.g. N = 3); eq. (18) is the definition and yields at least one ring
--   - encoding: ∑_k m_k = N − 2 → ∑_k m_k + 2 = N in ℕ; reason: avoids truncated subtraction; identical for N ≥ 2
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), proof of Theorem 4.3, Step 2, p. 30 (PDF 31)

import Definitions.Def_TerracedZonal_Excess_Stage1

namespace TerracedZonal.Excess

open Filter Topology

/-- Proof of Theorem 4.3, Step 2, p. 30 (PDF 31): for every family of Stage-1 outputs `m_N`,
`S(m_N) = C'(λ₀) N^{2/3} (1 + o(1))` with `λ₀ = c_step`, `C'(λ₀) = ⅔ C(λ₀)/λ₀`, and the seam
part `λ₀ S(m_N)` is two thirds of `G_{λ₀}(m_N)` in the limit. -/
theorem theorem_4_3_step2 (m : ∀ N : ℕ, Pops N)
    (hm : ∀ᶠ N : ℕ in atTop, IsStage1Output N (m N)) :
    Asymptotics.IsEquivalent atTop (fun N : ℕ => seamSum N (m N))
        (fun N : ℕ => (2 / 3) * (Cfun cStep / cStep) * (N : ℝ) ^ (2 / 3 : ℝ)) ∧
      Tendsto (fun N : ℕ => cStep * seamSum N (m N) / Gcost cStep N (m N)) atTop (𝓝 (2 / 3)) := by sorry

end TerracedZonal.Excess
