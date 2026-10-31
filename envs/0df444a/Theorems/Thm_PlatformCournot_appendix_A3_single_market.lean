-- Prove2me | Theorems.Thm_PlatformCournot_appendix_A3_single_market
-- name    : PlatformCournot.appendix_A3_single_market
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:14.706114+00:00
-- url     : https://prove2.me/theorems/55987c89-90ff-4a1b-b02a-9d4012f28c14
-- title:
--   Appendix A.3 — single market: minimum Nash welfare $\frac{(n+2)(\alpha_1-c_1)^2}{(3n+5)\beta_1}$, attained by $\bar C^*$
-- statement:
--   Let $n\ge 1$ and fix a market $j$; consider the game on the edge set $F\times\{j\}$, in which every firm can supply only market $j$.
--
--   1. For linear costs $\bar C_i(s)=(c_i s)^+$ with slopes $c_i\ge 0$ and $c_{\min}=\min_i c_i$, every Nash equilibrium $q$ of the game on $F\times\{j\}$ satisfies
--   $$\mathrm{SW}(q,\bar C)\ \ge\ \frac{(n+2)\bigl((\alpha_j-c_{\min})^+\bigr)^2}{(3n+5)\beta_j}.$$
--   2. For $0\le c_1<\alpha_j$, let $\bar C^*$ have slope $c_1$ for firm 1 and
--   $$c^*_i=\alpha_j-\frac{2n+3}{3n+5}(\alpha_j-c_1),\qquad i=2,\dots,n,$$
--   for the others. Then the game on $F\times\{j\}$ under $\bar C^*$ has a Nash equilibrium, and every Nash equilibrium $q$ of it has
--   $$\mathrm{SW}(q,\bar C^*)=\frac{(n+2)(\alpha_j-c_1)^2}{(3n+5)\beta_j}.$$
--
--   So, for a fixed cheapest slope $c_1$, the minimum welfare at Nash equilibrium over the other firms' slopes is $\frac{(n+2)(\alpha_j-c_1)^2}{(3n+5)\beta_j}$. Divided into the efficient welfare $(\alpha_j-c_1)^2/(2\beta_j)$ it gives the bound $\frac32(1-\frac1{3n+6})$ of Theorem 1. The page cites Johari and Tsitsiklis (2005, Theorem 12) for the optimization.
--
--   Differences from the source:
--   - encoding: firms 1, …, n and markets 1, …, m → Fin n and Fin m (0-based), supply profile q i j firm first; reason: relabelling only
--   - generalization: c₁ ≤ ⋯ ≤ c_n sorted without loss of generality, and c₁ → the minimum slope ⨅ i, c i of an unsorted profile; reason: for a sorted profile the minimum is c₁, so the statement specializes to the page's
--   - reading: linear costs C̄ᵢ(s) = (cᵢ s)⁺ → slopes cᵢ ≥ 0; reason: the paper's costs satisfy Assumption 1 (p.8), and (c s)⁺ vanishes on (−∞, 0] only when c ≥ 0
--   - generalization: the model with one market M = {1} → any market j of the m-market model, in the game on the edge set F × {j}; reason: equilibria on F × {j} supply nothing to the other markets, whose terms in SW vanish, and m = 1, j = 1 is the page's case; this is also the form used on p.30
--   - generalization: n ≥ 2 ("For the remainder of the proof, we restrict ourselves to n ≥ 2") → n ≥ 1; reason: at n = 1 the same formula is the monopoly welfare 3(α − c)²/(8β), and the n ≥ 2 statement is a special case
--   - generalization: c₁ < α₁ assumed without loss of generality → part 1 for every slope profile, with (α_j − c_min)⁺; reason: when c_min ≥ α_j the right side is 0 and the page's case c₁ < α₁ is the rest
--   - reading: "the minimum social welfare at Nash equilibrium is given by SW(qNE(F × {1}),C̄∗) = …" → part 1 (a lower bound for every linear profile) and part 2 (existence of a Nash equilibrium and equality under C̄∗ for 0 ≤ c₁ < α_j); reason: a minimum is a lower bound that is attained; c₁ ≥ 0 because the costs satisfy Assumption 1
--   - encoding: the unique Nash equilibrium q^NE → every Nash equilibrium q; reason: Lemma 1 makes the equilibrium unique, so a claim about every equilibrium is the claim about q^NE
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Appendix A.3, p.29

import Mathlib
import Definitions.Def_PlatformCournot_IsNash
import Definitions.Def_PlatformCournot_socialWelfare
import Definitions.Def_PlatformCournot_linearCost
import Definitions.Def_PlatformCournot_worstSlope

namespace PlatformCournot

/-- **Appendix A.3: minimum Nash welfare in a single market, attained by `C̄*`.**
Pang et al., arXiv:1903.04574v3, Appendix A.3, p.29: "Fixing α1, β1, c1, we can optimize over
c2,...,cn in order to minimize the social welfare at the unique Nash equilibrium of the Cournot game.
… Thus, for the fixed parameters α1,β1,c1, the minimum social welfare at Nash equilibrium is given by
SW(qNE(F × {1}),C̄∗) = (n + 2)(α1 − c1)² / ((3n + 5)β1)."

For `n ≥ 1` firms and a market `j`, in the game restricted to the edge set `F × {j}`:
(i) for linear costs `Cᵢ(s) = (cᵢ s)⁺` with `cᵢ ≥ 0`, every Nash equilibrium has welfare at least
`(n+2)((αⱼ − c_min)⁺)² / ((3n+5)βⱼ)`, `c_min = minᵢ cᵢ`;
(ii) for `0 ≤ c₁ < αⱼ`, under `C̄*` (slope `c₁` for the first firm and
`c*ᵢ = αⱼ − (2n+3)/(3n+5) · (αⱼ − c₁)` for the others) a Nash equilibrium exists and every Nash
equilibrium has welfare exactly `(n+2)(αⱼ − c₁)² / ((3n+5)βⱼ)`.

**Formalization Note** The single market `F × {j}` is the edge set `Set.univ ×ˢ {j}` inside the
`m`-market model: its equilibria supply nothing to the other markets, whose terms in `SW` vanish.
`c_min` is `⨅ i, c i`. The paper sorts `c₁ ≤ ⋯ ≤ cₙ`, assumes `c₁ < α₁` and argues `n ≥ 2`. -/
theorem appendix_A3_single_market {n m : ℕ} (D : AffineDemand m) (hn : 1 ≤ n) (j : Fin m) :
    (∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) →
      ∀ q, IsNash D (fun i => linearCost (c i)) (Set.univ ×ˢ {j}) q →
        ((n : ℝ) + 2) * (max (D.α j - ⨅ i, c i) 0) ^ 2 / ((3 * (n : ℝ) + 5) * D.β j) ≤
          socialWelfare D (fun i => linearCost (c i)) q) ∧
    (∀ c₁ : ℝ, 0 ≤ c₁ → c₁ < D.α j →
      (∃ q, IsNash D (fun i => linearCost (worstSlope n (D.α j) c₁ i)) (Set.univ ×ˢ {j}) q) ∧
      ∀ q, IsNash D (fun i => linearCost (worstSlope n (D.α j) c₁ i)) (Set.univ ×ˢ {j}) q →
        socialWelfare D (fun i => linearCost (worstSlope n (D.α j) c₁ i)) q =
          ((n : ℝ) + 2) * (D.α j - c₁) ^ 2 / ((3 * (n : ℝ) + 5) * D.β j)) := by sorry

end PlatformCournot
