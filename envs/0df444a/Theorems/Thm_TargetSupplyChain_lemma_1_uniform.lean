-- Prove2me | Theorems.Thm_TargetSupplyChain_lemma_1_uniform
-- name    : TargetSupplyChain.lemma_1_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:40.398468+00:00
-- url     : https://prove2.me/theorems/0802876a-aa49-49fd-b904-616f49234eab
-- title:
--   Lemma 1, uniform clause: the target-oriented retailer's order $y(w)$ (corrected: $w<p$, $\alpha^r<a+b$)
-- statement:
--   Let $0<c<p$, $a\ge0$, $b>0$, demand $D\sim U[a,a+b]$, and let the retailer's target coefficient satisfy $0<\alpha^r$ and $a\le\alpha^r<a+b$. For every wholesale price $w\in[c,p)$, the target-oriented retailer's problem (7),
--   $$\max_{y\ge0}\ \rho_{\tau^r}\big(V(y;D)\big),\qquad V(y;D)=p\min\{D,y\}-wy,\quad \tau^r=\alpha^r(p-w),$$
--   with $\rho$ the CVaR-satisficing measure, has exactly one solution $y(w)$, namely
--   $$
--   y(w)=\begin{cases}2\alpha^r-a, & w<p-\dfrac{2p(\alpha^r-a)}{b},\\[2mm] \dfrac{(p-w)(a+b)+2\alpha^r w}{p+w}, & w\ge p-\dfrac{2p(\alpha^r-a)}{b}.\end{cases}
--   $$
--
--   This is the retailer's reaction function in the "NT" game; the supplier's problem in Proposition 2 is solved against it.
--
--   Differences from the source:
--   - correction: second branch for w ∈ [p − 2p(αʳ − a)/b, p], so y(p) = αʳ → w ∈ [c, p); reason: at w = p the target is 0, every y ∈ [0, a] has CSM 1 and every y > a has CSM < 1, so the solutions are [0, a] (as p.13 says). Counterexample: (p, c, a, b, αʳ, w) = (10, 4, 1, 99, 10, 10), where ρ(V(1; D)) = 1 > ρ(V(10; D)) = 90/99 − 1
--   - correction: αʳ in the paper's target range [a, a + b] → αʳ < a + b; reason: at αʳ = a + b every order has CSM −1, so every y ≥ 0 solves (7) and y(w) is not the printed value. Counterexample: (p, c, a, b, αʳ, w) = (10, 4, 1, 99, 100, 5)
--   - reading: Lemma 1 states no range for αʳ → 0 < αʳ and a ≤ αʳ; reason: α positive (p.9); the lemma's proof works on a ≤ αʳ (p.A3), the range of Proposition 2; for αʳ < a/2 the first branch is negative
--   - reading: standing parameters: c ≤ w ≤ p (p.10), a and b non-negative (p.11), D continuously distributed with a density (p.10), α a positive number (p.9) → 0 < c < p, 0 ≤ a, 0 < b (and 0 < αʳ where αʳ appears); reason: b > 0 because U[a, a+b] has a density; c < p makes ξᶜ > 0 (Prop. 2 divides by ξᶜ); c > 0 is used by the paper's proofs (they divide by c) and keeps bξᶜ + a < a + b
--   - reading: CVaR_η(V) = E[V | V ≤ q_{1−η}(V)] for η ∈ [0,1) and E[V | V ≥ q_{−η}(V)] for η ∈ (−1,0), with q_η the unique η-quantile (Definition 1, p.6) → CVaR_η = average of the quantile function over (0, 1−η] (η ≥ 0), resp. over (−η, 1] (η < 0); reason: V(y; D) has an atom at (p − w)y, so the unique quantile does not exist; the quantile average equals the printed formula whenever it does, and is the form the Online Appendix computes with
--   - reading: "the retailer's order quantity as a function of w, y(w), is given as follows" → for every y: y solves (7) iff y equals the formula; reason: "the" order quantity asserts that the solution exists and is unique
--   - encoding: D uniformly distributed in [a, a+b]; E[min(y, D)] → the law (1/b)·Lebesgue restricted to [a, a+b]; E[min(y, D)] is the integral of min(d, y) against it; reason: Lean representation of the uniform law; the same instances
-- source:
--   Chen–Tang, Supply Chain Performance with Target-Oriented Firms, SSRN 3533746 (version of July 6, 2021), Online Appendix A, Lemma 1 (uniform clause), p.A1 (PDF 34); domain a ≤ αʳ from its proof, p.A3 (PDF 36)

import Mathlib
import Definitions.Def_TargetSupplyChain_Model

namespace TargetSupplyChain

/-- **Lemma 1, uniform clause** (corrected: `w < p`, `αʳ < a + b`), Chen–Tang, *Supply Chain
Performance with Target-Oriented Firms*, SSRN 3533746 (version of July 6, 2021), Online
Appendix A, Lemma 1, p.A1 (PDF 34).

For demand `D ~ U[a, a + b]`, target coefficient `αʳ` with `0 < αʳ`, `a ≤ αʳ < a + b`, and
wholesale price `w ∈ [c, p)`, the target-oriented retailer's problem (7) with target
`τʳ = αʳ(p − w)` has exactly one solution `y(w)`:

* `y(w) = 2αʳ − a` if `w < p − 2p(αʳ − a)/b`;
* `y(w) = ((p − w)(a + b) + 2αʳw)/(p + w)` if `w ≥ p − 2p(αʳ − a)/b`.

**Formalization Note** The printed lemma states the second branch on `[p − 2p(αʳ − a)/b, p]`.
At `w = p` the target is `0`, every `y ∈ [0, a]` has CSM `1` and every `y > a` has CSM below
`1`, so the solutions are `[0, a]` and not `αʳ`; `w = p` is excluded (the supplier's set is
`[c, p)`). `αʳ = a + b` is excluded (every order then has CSM `−1`). `αʳ ≥ a` is the domain of
the lemma's proof (p.A3) and of Proposition 2. The CSM is built from the quantile-average
extended CVaR (`extCVaR`). -/
theorem lemma_1_uniform (P : Params) (hP : P.Standing) (α : ℝ) (hα : P.InDom α)
    (w : ℝ) (hw : w ∈ Set.Ico P.c P.p) :
    ∀ y : ℝ, IsTOBestResponse P α w y ↔
      y = if w < P.p - 2 * P.p * (α - P.a) / P.b then 2 * α - P.a
        else ((P.p - w) * (P.a + P.b) + 2 * α * w) / (P.p + w) := by sorry

end TargetSupplyChain
