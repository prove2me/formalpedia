-- Prove2me | Theorems.Thm_SinglePointPricing_Det_Supplement_theorem_4
-- name    : SinglePointPricing.Det.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:34:11.353347+00:00
-- url     : https://prove2.me/theorems/8a8017c7-33a3-41c3-b3a1-e8ccee611779
-- title:
--   Theorem 4 (corrected: grid coverage, indexing, terminal oracle) — interval-information maximin ratio
-- statement:
--   Fix $\alpha\in[0,1]$ and $0<q_l<q_h<1$. For every $w>0$, integer $N\ge1$, and strictly increasing positive grid $A=(a_0,\ldots,a_{2N+1})$ with $a_{N+1}=w$ and $a_0\le\underline r_\alpha(w,q_l)$, the corrected interval program (LP-int) attains its value at nonnegative price weights summing to one. Every feasible probability-weight vector at objective $c$ defines a nonnegative price law $\Psi_{A,p}$ with
--   $$
--   \inf_{F\in\mathcal F_\alpha(w,[q_l,q_h])}R(\Psi_{A,p},F)\ge c,\qquad
--   \mathcal R(\mathcal P,\mathcal F_\alpha(w,[q_l,q_h]))\ge\underline L_{\alpha,q_l,q_h,A}.
--   $$
--   There is also a constant $C>0$, depending only on $\alpha,q_l,q_h$, such that for every $w>0$ and every $N>1$ there is a strictly increasing positive grid of this size with $a_0=\underline r_\alpha(w,q_l)$ and $a_{N+1}=w$ for which
--   $$
--   \mathcal R(\mathcal P,\mathcal F_\alpha(w,[q_l,q_h]))\le\underline L_{\alpha,q_l,q_h,A}+\frac{C}{\sqrt N}.
--   $$
--   The class $\mathcal F_\alpha(w,[q_l,q_h])$ contains every admissible value law, not just the two endpoint-data families. The program therefore approximates the robust optimum when the conversion rate is known only within an interval. Propositions F-1 and F-2 support this companion theorem.
--
--   **Formalization Note** Part 1 needs first-point coverage: at $\alpha=0,w=1,q_l=1/2,q_h=1361/2500,N=2$, the grid $(0.855,0.877,0.886,1,1.619,4.659)$ has optimal value about $0.50957971$, but the exact optimal price law has ratio about $0.49102413$ at $r=196621/250000$ in the low family. The exact primal/dual certificates are retained. The displayed maximin inequality is false as printed as well: at $\alpha=0,w=1,q_l=10^{-9},q_h=1/2$ and the printed four-point grid $(0.9,0.95,1,2)$ the LP value is at least $9/19$, while the maximin ratio is at most $0.352778$. The program indexing follows the proof's (F-2), and the terminal oracle handles an empty high-parameter family as described below. In part 1 the index shift turns the printed condition $n>1$ on the grid $a_1,\ldots,a_{2n}$ into $N=n-1\ge1$; part 2 is printed in the zero-based indexing and keeps $N>1$.
--
--   Differences from the source:
--   - correction: part 1 permits arbitrary positive increasing grids with a_{N+1}=w → also require a_0 ≤ r̲_α(w,q_l); reason: the grid (0.855,0.877,0.886,1,1.619,4.659) at α=0,w=1,q_l=1/2,q_h=1361/2500,N=2 has optimal value 0.50957971 but its optimal law has ratio 0.49102413 at r=196621/250000; first-point coverage repairs the missing low-parameter interval; the printed maximin inequality fails too: at α=0,w=1,q_l=10⁻⁹,q_h=1/2, with the printed N=2 grid (0.9,0.95,1,2) one has L ≥ 9/19 and R ≤ 0.352778
--   - correction: (LP-int) and part 1 use indices 1..2N while part 2 and the proof use 0..2N+1 and the last row needs a further endpoint → use points and rows 0..2N+1, low rows 0..N and high rows N+1..2N+1; part 1 is quantified over N ≥ 1 and part 2 over N > 1; reason: these are exactly the summation and row ranges in the proof display (F-2), App-40–41; the terminal endpoint is supplied by its high-branch oracle; a printed part-1 grid a_1..a_{2n} with n > 1 has n points below w and n from w on, so it is the zero-based grid with N = n−1 ≥ 1, and requiring N > 1 there would drop the printed case n = 2
--   - correction: the last constraint reads the undefined next grid endpoint; Appendix F appends r̄_α, which may be below w → the last row uses w ṽ_α / Γ_α⁻¹(q), the saturated high-branch oracle; reason: this equals the endpoint oracle when r̄_α ≥ w and its limit at infinity for α=0; when α=1, w=1, q=e⁻², a literal low-branch endpoint gives 1/2 instead of 1/(2e), forcing every LP value ≤1/e although the maximin ratio is at least 1/2; see DISPROOF.md and Appendix F, App-40, App-46–48
--   - generalization: the optimal LP solution has a price-law performance guarantee → normalized attainment and the guarantee for every feasible probability-weight vector at its objective c; reason: every normalized optimizer is one of these vectors, so the full source guarantee and the maximin lower bound are included
--   - encoding: O(1/√N) with constants depending only on α, q_l and q_h → ∃ C > 0, ∀ w > 0, ∀ N > 1, ∃ A with the bound C/√N; reason: states the full scale-independent source constant; the grid starts exactly at r̲_α(w,q_l) in this clause
--   - encoding: laws F, pricing cdfs Ψ, and infima of performance ratios → the published probability-measure interfaces and real suprema and infima; reason: same base mission conventions; nonnegative value laws have finite positive mean, making their oracle positive and all mechanism ratios integrable and in [0,1]
--   - encoding: w is the historical price and α and the conversion rates satisfy the standing model assumptions → w > 0, α ∈ [0,1], and all conversion endpoints lie in (0,1); reason: pp. 8–11 and the Appendix F context exclude undefined or infeasible data; these are the standing assumptions, not additional regularity
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p) of the published Setting; reason: p. 2 speaks of values greater than or equal to w and Rev uses 1{v ≥ p}; with the strict tail the terminal atoms of the worst-case family would sell with probability 0 at their own price
--   - reading: α-strong regularity: a positive density on the support, except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (printed non-increasing on p. 11) → the published IsAlphaSR: Γ_α⁻¹ ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: non-increasing is a slip for non-decreasing (the same page defines regular laws by a non-decreasing virtual value); the convexity form is that condition and allows the atom at the top of the support
--   - reading: increasing sequence of reals → strictly increasing on the finite index range; reason: a grid lists distinct prices; the programs require a_N < w = a_{N+1}, and a_N < w is derived from this
--   - encoding: a finite grid and its weights; P_A is printed on indices 1..N with a_i inside the sum over j → sequences ℕ → ℝ read only on the finite index range; P_A is the Dirac mixture Σ_j p_j δ_{a_j} on that range; reason: values outside the range are never read; a_i inside the sum is an index slip for a_j, and shifting the first index does not change the set of laws
--   - encoding: the LP maximum and the one-sided limits in its normalisers → sSup of the feasible objectives and limUnder along the left neighbourhood; reason: the objective set is nonempty and bounded above and attainment is a conclusion; the left limits exist at every positive grid point
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Theorem 4, pp. 30–31; (LP-int), p. 30; (F-2), pp. App-40–41; Appendix F, pp. App-42–49

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Supplement_LPint

namespace SinglePointPricing.Det.Supplement

open MeasureTheory

/-- Theorem 4, corrected using the proof's (F-2) indexing, the missing lower
grid coverage premise, and the saturated terminal high-branch oracle.
Part 1 takes `1 ≤ N`: its printed grid `1..2n` with `n > 1` is the grid `0..2N+1`
with `n = N + 1`. Part 2 keeps `1 < N`, as its printed grid is already `0..2N+1`.
The approximation constant depends on `α, ql, qh` only. -/
theorem theorem_4 (α ql qh : ℝ) (hα : α ∈ Set.Icc 0 1)
    (hql : ql ∈ Set.Ioo 0 1) (hqh : qh ∈ Set.Ioo 0 1) (hlh : ql < qh) :
    (∀ (w : ℝ) (N : ℕ) (a : ℕ → ℝ), 0 < w → 1 ≤ N →
      IncreasingGrid a (2 * N + 2) → PositiveGrid a (2 * N + 2) →
      a (N + 1) = w → a 0 ≤ rLow α w ql →
      (∃ p : ℕ → ℝ, GridWeights p (2 * N + 2) ∧
        LPintFeasible α w ql qh a N p (LPintVal α w ql qh a N)) ∧
      (∀ (p : ℕ → ℝ) (c : ℝ), LPintFeasible α w ql qh a N p c →
        GridWeights p (2 * N + 2) →
        IsMech (gridMech a p (2 * N + 2)) ∧
          c ≤ sInf (ratio (gridMech a p (2 * N + 2)) '' FClassI α w ql qh)) ∧
      LPintVal α w ql qh a N ≤ maximin {Ψ | IsMech Ψ} (FClassI α w ql qh)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (w : ℝ) (N : ℕ), 0 < w → 1 < N →
      ∃ a : ℕ → ℝ, IncreasingGrid a (2 * N + 2) ∧ PositiveGrid a (2 * N + 2) ∧
        a 0 = rLow α w ql ∧ a (N + 1) = w ∧
        maximin {Ψ | IsMech Ψ} (FClassI α w ql qh) ≤
          LPintVal α w ql qh a N + C / Real.sqrt N) := by sorry

end SinglePointPricing.Det.Supplement
