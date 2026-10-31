-- Prove2me | Theorems.Thm_TargetSupplyChain_proposition_8
-- name    : TargetSupplyChain.proposition_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:11.325766+00:00
-- url     : https://prove2.me/theorems/fdb644ea-db64-4bbd-99bc-cc6ea33a5a2b
-- title:
--   Proposition 8: NT vs NN supply-chain profit — thresholds, concavity, maximum and first-best at $\alpha^r=b\xi^c+a$ (corrected: $\alpha^r<a+b$)
-- statement:
--   Let $0<c<p$, $a\ge0$, $b>0$, demand $D\sim U[a,a+b]$, $\xi^c=(p-c)/p$, and let the retailer's target coefficient range over
--   $$\mathrm{Dom}=\{\alpha^r:\ 0<\alpha^r,\ a\le\alpha^r<a+b\}.$$
--   For a decision pair $(w,y)$ let $\Pi=\pi^s+\pi^r=(w-c)y+p\,\mathbb E[\min(D,y)]-wy$ be the total supply-chain profit, and write $\Pi^*_{nt}$ and $\Pi^*_{nn}$ for its value at an NT and an NN outcome. Then NN outcomes exist, NT outcomes exist for every $\alpha^r\in\mathrm{Dom}$, and there are two thresholds $\bar\alpha^{r1}_I,\bar\alpha^{r2}_I$ such that:
--
--   1. for $\alpha^r\in\mathrm{Dom}$ with $\alpha^r\le\bar\alpha^{r1}_I$ or $\alpha^r\ge\bar\alpha^{r2}_I$, $\Pi^*_{nt}\le\Pi^*_{nn}$; and for $\alpha^r\in\mathrm{Dom}\cap(\bar\alpha^{r1}_I,\bar\alpha^{r2}_I)$, $\Pi^*_{nt}\ge\Pi^*_{nn}$;
--   2. $\Pi^*_{nt}$ is concave in $\alpha^r$ on $\mathrm{Dom}\cap[\bar\alpha^{r1}_I,a+b)$, and achieves its maximum (over all of $\mathrm{Dom}$) at $\alpha^r=b\xi^c+a$, which lies in $\mathrm{Dom}\cap[\bar\alpha^{r1}_I,a+b)$;
--   3. when $\alpha^r=b\xi^c+a$,
--   $$\Pi^*_{nt}=\Pi^{c*}_{nn}=\max_{y\ge0}\ p\,\mathbb E[\min(y,D)]-cy,$$
--   i.e., the supply chain's profit with a target-oriented retailer equals that of the risk-neutral centralized system.
--
--   The comparisons in part 1 hold between every NT outcome and every NN outcome. "Concave" in part 2 means: there is a function $G$, concave on $\mathrm{Dom}\cap[\bar\alpha^{r1}_I,a+b)$, with $\Pi^*_{nt}=G(\alpha^r)$ at every NT outcome for every $\alpha^r$ in that set. One pair of thresholds serves parts 1 and 2.
--
--   Part 3 is the paper's coordination result: with a target-oriented retailer, a plain wholesale-price contract can achieve the first-best supply-chain profit, which it cannot with a risk-neutral retailer.
--
--   Differences from the source:
--   - correction: αʳ ∈ [a, a + b] (Prop. 2) and αʳ ∈ [ᾱʳ¹_I, a + b] (Prop. 8) → αʳ < a + b; reason: at αʳ = a + b the target (a+b)(p − w) exceeds V(y; D) almost surely for every order y and every w < p, so every order has CSM −1, every y ≥ 0 is a best response and the supplier's profit is unbounded: the NT decisions are undefined. Counterexample: (p, c, a, b, αʳ) = (10, 4, 1, 99, 100)
--   - reading: the supplier maximizes (w − c)y over c ≤ w ≤ p (4); the solution is written w* = p − ε, y* = αʳ − ε with ε "an infinitely small positive number" (p.12) → an outcome is a limit (w*, y*) of pairs (wₙ, yₙ) with wₙ ∈ [c, p), yₙ a best response to wₙ, and (wₙ − c)yₙ tending to the supremum of the supplier's profit; profits are evaluated at the limit pair; reason: at w = p every y ∈ [0, a] is a best response (p.13: the supplier "will avert from setting the wholesale price to be equal to the retail price"), and for αʳ > a the supremum over w < p is not attained; p − ε, αʳ − ε are the limits p, αʳ
--   - reading: CVaR_η(V) = E[V | V ≤ q_{1−η}(V)] for η ∈ [0,1) and E[V | V ≥ q_{−η}(V)] for η ∈ (−1,0), with q_η the unique η-quantile (Definition 1, p.6) → CVaR_η = average of the quantile function over (0, 1−η] (η ≥ 0), resp. over (−η, 1] (η < 0); reason: V(y; D) has an atom at (p − w)y, so the unique quantile does not exist; the quantile average equals the printed formula whenever it does, and is the form the Online Appendix computes with
--   - reading: standing parameters: c ≤ w ≤ p (p.10), a and b non-negative (p.11), D continuously distributed with a density (p.10), α a positive number (p.9) → 0 < c < p, 0 ≤ a, 0 < b (and 0 < αʳ where αʳ appears); reason: b > 0 because U[a, a+b] has a density; c < p makes ξᶜ > 0 (Prop. 2 divides by ξᶜ); c > 0 is used by the paper's proofs (they divide by c) and keeps bξᶜ + a < a + b
--   - reading: part 2: "achieve its maximum at αʳ = bξᶜ + a" → Π*_nt at every NT outcome for every αʳ ∈ Dom is at most its value at αʳ = bξᶜ + a; reason: the stronger of the two readings (maximum over the whole range, not only over [ᾱʳ¹_I, a + b)); it is the statement the paper's discussion uses
--   - reading: "Π*_nt is concave in αʳ"; "Π*_nt ≤ Π*_nn" → there is G concave on Dom ∩ [ᾱʳ¹_I, a + b) with Π*_nt = G(αʳ) at every NT outcome; comparisons hold for every NT and every NN outcome; NN and NT outcomes exist; reason: Π*_nt and Π*_nn are the profits at the (unique) equilibrium decisions; existence rules out a vacuous statement
--   - encoding: Πᶜ*_nn, the maximum supply chain profit of the centralized system (8) → the greatest element of {p E[min(y, D)] − c y : y ≥ 0}; reason: Lean form of a maximum; the same value
--   - encoding: D uniformly distributed in [a, a+b]; E[min(y, D)] → the law (1/b)·Lebesgue restricted to [a, a+b]; E[min(y, D)] is the integral of min(d, y) against it; reason: Lean representation of the uniform law; the same instances
-- source:
--   Chen–Tang, Supply Chain Performance with Target-Oriented Firms, SSRN 3533746 (version of July 6, 2021), §5.1, Proposition 8, p.18 (Π*_nt and Π*_nn defined just above it, p.18); proof in Online Appendix A, p.A7 (PDF 40)

import Mathlib
import Definitions.Def_TargetSupplyChain_Model

namespace TargetSupplyChain

/-- **Proposition 8** (corrected: `αʳ < a + b`), Chen–Tang, *Supply Chain Performance with
Target-Oriented Firms*, SSRN 3533746 (version of July 6, 2021), §5.1, p.18.

Let demand be `D ~ U[a, a + b]`, `0 < c < p`, `0 ≤ a`, `0 < b`, and let the retailer's target
coefficient range over `Dom = {αʳ : 0 < αʳ, a ≤ αʳ < a + b}`. Write `Π*_nt = πˢ*_nt + πʳ*_nt`
and `Π*_nn = πˢ*_nn + πʳ*_nn` for the total supply-chain profit at an NT and an NN outcome.
NN outcomes exist, NT outcomes exist for every `αʳ ∈ Dom`, and there are two thresholds
`ᾱʳ¹_I`, `ᾱʳ²_I` such that:

1. `Π*_nt ≤ Π*_nn` if `αʳ ≤ ᾱʳ¹_I` or `αʳ ≥ ᾱʳ²_I`, and `Π*_nt ≥ Π*_nn` if
   `αʳ ∈ (ᾱʳ¹_I, ᾱʳ²_I)`;
2. `Π*_nt` is concave in `αʳ` on `[ᾱʳ¹_I, a + b)` and achieves its maximum (over all of `Dom`)
   at `αʳ = bξᶜ + a`;
3. at `αʳ = bξᶜ + a`, `Π*_nt = Πᶜ*_nn`, the maximum of the centralized profit (8).

**Formalization Note** One pair of thresholds serves parts 1 and 2. Part 1 compares every NT
outcome with every NN outcome. Part 2: `Π*_nt` agrees at every NT outcome with a function
`G` of `αʳ` concave on `[ᾱʳ¹_I, a + b) ∩ Dom`, the point `bξᶜ + a` lies in that set, and
`G(bξᶜ + a)` bounds `Π*_nt` on all of `Dom`. Part 3: `Π*_nt` at every NT outcome for
`αʳ = bξᶜ + a` is the greatest value of `Πᶜ_nn` on `[0, ∞)`. The printed ranges end at
`a + b`, where the NT outcome is undefined (every order has CSM `−1`); `a + b` is excluded.
Outcomes are limits of supplier-optimal sequences over `w ∈ [c, p)` (the paper's "p − ε");
profits are evaluated at the limit pair. -/
theorem proposition_8 (P : Params) (hP : P.Standing) :
    (∃ w y : ℝ, nnOutcome P w y) ∧
    (∀ α : ℝ, P.InDom α → ∃ w y : ℝ, ntOutcome P α w y) ∧
    ∃ α₁ α₂ : ℝ,
      (∀ α : ℝ, P.InDom α → (α ≤ α₁ ∨ α₂ ≤ α) →
        ∀ w y w' y' : ℝ, ntOutcome P α w y → nnOutcome P w' y' →
          totalProfit P w y ≤ totalProfit P w' y') ∧
      (∀ α : ℝ, P.InDom α → α₁ < α → α < α₂ →
        ∀ w y w' y' : ℝ, ntOutcome P α w y → nnOutcome P w' y' →
          totalProfit P w' y' ≤ totalProfit P w y) ∧
      (∃ G : ℝ → ℝ,
        ConcaveOn ℝ {α : ℝ | P.InDom α ∧ α₁ ≤ α} G ∧
        (∀ α : ℝ, P.InDom α → α₁ ≤ α → ∀ w y : ℝ, ntOutcome P α w y → totalProfit P w y = G α) ∧
        P.InDom (P.b * P.xi + P.a) ∧ α₁ ≤ P.b * P.xi + P.a ∧
        (∀ α : ℝ, P.InDom α → ∀ w y : ℝ, ntOutcome P α w y →
          totalProfit P w y ≤ G (P.b * P.xi + P.a))) ∧
      (∀ w y : ℝ, ntOutcome P (P.b * P.xi + P.a) w y →
        IsGreatest (centralProfit P '' Set.Ici 0) (totalProfit P w y)) := by sorry

end TargetSupplyChain
