-- Prove2me | Theorems.Thm_TargetSupplyChain_prop6_proof_ynt_le_ynn
-- name    : TargetSupplyChain.prop6_proof_ynt_le_ynn
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:43.23902+00:00
-- url     : https://prove2.me/theorems/bf8f4431-5bb5-4c86-ae59-563a72a3ffe1
-- title:
--   Proof of Proposition 6, case (2): $y^*_{nt}=y^1_{nt}\le y^*_{nn}$ for $\alpha^r\in[\alpha^{r1}_{nt},\alpha^{r2}_{nt})$
-- statement:
--   Let $0<c<p$, $a\ge0$, $b>0$, demand $D\sim U[a,a+b]$, $\xi^c=(p-c)/p$, and assume $b/a>2/\xi^c$. Let the target coefficient satisfy $0<\alpha^r$, $a\le\alpha^r<a+b$ and
--   $$\alpha^{r1}_{nt}\le\alpha^r<\alpha^{r2}_{nt}.$$
--   Then every NT outcome $(w^*_{nt},y^*_{nt})$ has
--   $$y^*_{nt}=y^1_{nt}\le y^*_{nn}$$
--   for every NN outcome $(w^*_{nn},y^*_{nn})$.
--
--   In this middle regime the target-oriented retailer orders no more than the risk-neutral one. The proof of Proposition 8 uses this step to show that the NT supply-chain profit is below the NN one there.
--
--   Differences from the source:
--   - reading: case (2) headed "For 0 ≤ b/a < 2/ξᶜ" (the same header as case (1)) → 2a < bξᶜ (b/a > 2/ξᶜ); reason: case (2) is the complement of case (1); the regime [αʳ¹_nt, αʳ²_nt) occurs only for b/a > 2/ξᶜ (Proposition 2)
--   - reading: the supplier maximizes (w − c)y over c ≤ w ≤ p (4); the solution is written w* = p − ε, y* = αʳ − ε with ε "an infinitely small positive number" (p.12) → an outcome is a limit (w*, y*) of pairs (wₙ, yₙ) with wₙ ∈ [c, p), yₙ a best response to wₙ, and (wₙ − c)yₙ tending to the supremum of the supplier's profit; profits are evaluated at the limit pair; reason: at w = p every y ∈ [0, a] is a best response (p.13: the supplier "will avert from setting the wholesale price to be equal to the retail price"), and for αʳ > a the supremum over w < p is not attained; p − ε, αʳ − ε are the limits p, αʳ
--   - reading: standing parameters: c ≤ w ≤ p (p.10), a and b non-negative (p.11), D continuously distributed with a density (p.10), α a positive number (p.9) → 0 < c < p, 0 ≤ a, 0 < b (and 0 < αʳ where αʳ appears); reason: b > 0 because U[a, a+b] has a density; c < p makes ξᶜ > 0 (Prop. 2 divides by ξᶜ); c > 0 is used by the paper's proofs (they divide by c) and keeps bξᶜ + a < a + b
--   - reading: CVaR_η(V) = E[V | V ≤ q_{1−η}(V)] for η ∈ [0,1) and E[V | V ≥ q_{−η}(V)] for η ∈ (−1,0), with q_η the unique η-quantile (Definition 1, p.6) → CVaR_η = average of the quantile function over (0, 1−η] (η ≥ 0), resp. over (−η, 1] (η < 0); reason: V(y; D) has an atom at (p − w)y, so the unique quantile does not exist; the quantile average equals the printed formula whenever it does, and is the form the Online Appendix computes with
--   - encoding: y*_nt = y¹_nt ≤ y*_nn → every NT outcome's order equals y¹_nt and is at most every NN outcome's order; reason: the decisions are the outcomes of the two games, which are unique (Proposition 2, (9)–(10))
--   - encoding: D uniformly distributed in [a, a+b]; E[min(y, D)] → the law (1/b)·Lebesgue restricted to [a, a+b]; E[min(y, D)] is the integral of min(d, y) against it; reason: Lean representation of the uniform law; the same instances
-- source:
--   Chen–Tang, Supply Chain Performance with Target-Oriented Firms, SSRN 3533746 (version of July 6, 2021), Online Appendix A, proof of Proposition 6, case (2), p.A6 (PDF 39); cited in the proof of Proposition 8, part 2(2), p.A7 (PDF 40)

import Mathlib
import Definitions.Def_TargetSupplyChain_Model
import Definitions.Def_TargetSupplyChain_ClosedForms

namespace TargetSupplyChain

/-- **Proof of Proposition 6, case (2): `y*_nt = y¹_nt ≤ y*_nn`**, Chen–Tang, *Supply Chain
Performance with Target-Oriented Firms*, SSRN 3533746 (version of July 6, 2021), Online
Appendix A, proof of Proposition 6, case (2), p.A6 (PDF 39).

For demand `D ~ U[a, a + b]` with `b/a > 2/ξᶜ` and a target coefficient
`αʳ ∈ [αʳ¹_nt, αʳ²_nt)` (with `0 < αʳ`, `a ≤ αʳ < a + b`), every NT outcome orders
`y*_nt = y¹_nt`, and this order is at most the order `y*_nn` of every NN outcome.

**Formalization Note** The case is headed "For 0 ≤ b/a < 2/ξᶜ" in the source, the same as
case (1); it is the complement `b/a > 2/ξᶜ`, written `2a < bξᶜ`, the only regime in which
`[αʳ¹_nt, αʳ²_nt)` occurs (Proposition 2). Outcomes are limits of supplier-optimal sequences
over `w ∈ [c, p)`. -/
theorem prop6_proof_ynt_le_ynn (P : Params) (hP : P.Standing) (h2 : 2 * P.a < P.b * P.xi)
    (α : ℝ) (hα : P.InDom α) (h1 : alphaR1 P ≤ α) (h2' : α < alphaR2 P) :
    ∀ w y : ℝ, ntOutcome P α w y →
      y = y1nt P α ∧ ∀ w' y' : ℝ, nnOutcome P w' y' → y ≤ y' := by sorry

end TargetSupplyChain
