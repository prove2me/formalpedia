-- Prove2me | Theorems.Thm_SinglePointPricing_Det_Supplement_theorem_3
-- name    : SinglePointPricing.Det.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:31:56.525428+00:00
-- url     : https://prove2.me/theorems/8e493aac-2761-4706-a266-48d4acd807df
-- title:
--   Theorem 3 (corrected: grid coverage and terminal oracle) — randomized maximin ratio
-- statement:
--   Fix $\alpha\in[0,1]$ and $q\in(0,1)$. For every $w>0$, every integer $N>1$, and every strictly increasing positive grid $A=(a_0,\ldots,a_{2N})$ with $a_{N+1}=w$ and $a_0\le\underline r_\alpha(w,q)$, the corrected program (LP) has an optimizer whose nonnegative price weights sum to one. Every feasible pair $(p,c)$ with total weight one defines a pricing mechanism $\Psi_{A,p}=\sum_jp_j\delta_{a_j}$ satisfying
--   $$
--   \inf_{F\in\mathcal F_\alpha(w,q)}R(\Psi_{A,p},F)\ge c,\qquad
--   \mathcal R(\mathcal P,\mathcal F_\alpha(w,q))\ge\underline L_{\alpha,q,A}.
--   $$
--   Furthermore, there is a constant $C>0$, depending only on $\alpha$ and $q$, such that for every $w>0$ and every $N>1$ there is such a grid with
--   $$
--   \mathcal R(\mathcal P,\mathcal F_\alpha(w,q))\le\underline L_{\alpha,q,A}+\frac{C}{\sqrt N}.
--   $$
--   Here $\mathcal P$ is the class of all nonnegative randomized prices, $\mathcal F_\alpha(w,q)$ is the whole class of α-strongly regular value laws with conversion $q$ at $w$, $R$ is revenue divided by oracle revenue, and $\underline L$ is the explicit finite LP value. Thus the program supplies both a mechanism and an approximation to its optimal robust performance, uniformly in the price scale.
--
--   **Formalization Note** The source's unrestricted first grid point is false: at $\alpha=0,w=1,q=1/2,N=2,A=(0.9,0.95,0.98,1,3)$, an exact optimal LP law has value about $0.53796044$ but performance at a rational low-family parameter $r=423533/500000$ about $0.53534545$. Exact primal/dual certificates are retained in evidence/lp_counterexamples.json. The displayed maximin inequality is false as printed as well: at $\alpha=0,w=1,q=10^{-9}$ and $A=(0.8,0.9,0.95,1,2)$ the LP value is at least $4/5$, while the maximin ratio is at most $0.352778$ (evidence/check_maximin_refutation.py). The additional first-point condition covers the missed parameter interval. The terminal oracle and the apparent grid-size typo in part (ii) are resolved explicitly in the definitions and differences below.
--
--   Differences from the source:
--   - correction: part (i) permits arbitrary positive increasing A with a_{N+1}=w → also require a_0 ≤ r̲_α(w,q); reason: the grid (0.9,0.95,0.98,1,3) at α=0,w=1,q=1/2,N=2 has an optimal LP value 0.53796044 but its optimal mechanism has ratio 0.53534545 at r=423533/500000; Appendix F starts at r̲_α and the extra coverage condition repairs the missing interval; the printed maximin inequality fails too: at α=0,w=1,q=10⁻⁹,A=(0.8,0.9,0.95,1,2) one has L ≥ 4/5 and R ≤ 0.352778
--   - correction: the last constraint reads the undefined next grid endpoint; Appendix F appends r̄_α, which may be below w → the last row uses w ṽ_α / Γ_α⁻¹(q), the saturated high-branch oracle; reason: this equals the endpoint oracle when r̄_α ≥ w and its limit at infinity for α=0; when α=1, w=1, q=e⁻², a literal low-branch endpoint gives 1/2 instead of 1/(2e), forcing every LP value ≤1/e although the maximin ratio is at least 1/2; see DISPROOF.md and Appendix F, App-40, App-46–48
--   - reading: part (ii) writes a sequence indexed 0..N while evaluating (LP) → the approximation grid has indices 0..2N, satisfies the same LP grid hypotheses and first-point coverage; reason: the displayed value is that of (LP), whose grid is defined immediately above; using an unrelated grid would not assert convergence of the lower bounds
--   - generalization: the optimal LP solution has a price-law performance guarantee → normalized attainment and the guarantee for every feasible probability-weight vector at its objective c; reason: every normalized optimizer is one of these vectors, so the full source guarantee and the maximin lower bound are included
--   - encoding: O(1/√N) with constants depending only on α and q → ∃ C > 0, ∀ w > 0, ∀ N > 1, ∃ A with the bound C/√N; reason: states the scale-independent source constant with its full quantifier order
--   - encoding: laws F, pricing cdfs Ψ, and infima of performance ratios → the published probability-measure interfaces and real suprema and infima; reason: same base mission conventions; nonnegative value laws have finite positive mean, making their oracle positive and all mechanism ratios integrable and in [0,1]
--   - encoding: w is the historical price and α and the conversion rates satisfy the standing model assumptions → w > 0, α ∈ [0,1], and all conversion endpoints lie in (0,1); reason: pp. 8–11 and the Appendix F context exclude undefined or infeasible data; these are the standing assumptions, not additional regularity
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p) of the published Setting; reason: p. 2 speaks of values greater than or equal to w and Rev uses 1{v ≥ p}; with the strict tail the terminal atoms of the worst-case family would sell with probability 0 at their own price
--   - reading: α-strong regularity: a positive density on the support, except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (printed non-increasing on p. 11) → the published IsAlphaSR: Γ_α⁻¹ ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: non-increasing is a slip for non-decreasing (the same page defines regular laws by a non-decreasing virtual value); the convexity form is that condition and allows the atom at the top of the support
--   - reading: increasing sequence of reals → strictly increasing on the finite index range; reason: a grid lists distinct prices; the programs require a_N < w = a_{N+1}, and a_N < w is derived from this
--   - encoding: a finite grid and its weights; P_A is printed on indices 1..N with a_i inside the sum over j → sequences ℕ → ℝ read only on the finite index range; P_A is the Dirac mixture Σ_j p_j δ_{a_j} on that range; reason: values outside the range are never read; a_i inside the sum is an index slip for a_j, and shifting the first index does not change the set of laws
--   - encoding: the LP maximum and the one-sided limits in its normalisers → sSup of the feasible objectives and limUnder along the left neighbourhood; reason: the objective set is nonempty and bounded above and attainment is a conclusion; the left limits exist at every positive grid point
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Theorem 3, p. 26; (LP), pp. 25–26; Appendix F, pp. App-40–49

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Supplement_LP

namespace SinglePointPricing.Det.Supplement

open MeasureTheory

/-- Theorem 3, corrected at the first and terminal grid endpoints.
The constant is uniform in the scale `w` as well as the grid size `N`.
The first part states normalized attainment, the mechanism guarantee for
all feasible probability weights, and the maximin lower bound. -/
theorem theorem_3 (α q : ℝ) (hα : α ∈ Set.Icc 0 1) (hq : q ∈ Set.Ioo 0 1) :
    (∀ (w : ℝ) (N : ℕ) (a : ℕ → ℝ), 0 < w → 1 < N →
      IncreasingGrid a (2 * N + 1) → PositiveGrid a (2 * N + 1) →
      a (N + 1) = w → a 0 ≤ rLow α w q →
      (∃ p : ℕ → ℝ, GridWeights p (2 * N + 1) ∧
        LPFeasible α w q a N p (LPval α w q a N)) ∧
      (∀ (p : ℕ → ℝ) (c : ℝ), LPFeasible α w q a N p c →
        GridWeights p (2 * N + 1) →
        IsMech (gridMech a p (2 * N + 1)) ∧
          c ≤ sInf (ratio (gridMech a p (2 * N + 1)) '' FClass α w q)) ∧
      LPval α w q a N ≤ maximin {Ψ | IsMech Ψ} (FClass α w q)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (w : ℝ) (N : ℕ), 0 < w → 1 < N →
      ∃ a : ℕ → ℝ, IncreasingGrid a (2 * N + 1) ∧ PositiveGrid a (2 * N + 1) ∧
        a (N + 1) = w ∧ a 0 ≤ rLow α w q ∧
        maximin {Ψ | IsMech Ψ} (FClass α w q) ≤ LPval α w q a N + C / Real.sqrt N) := by sorry

end SinglePointPricing.Det.Supplement
