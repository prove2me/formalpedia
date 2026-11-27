-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_3_6
-- name    : TradingPostNSW.Leontief.Supplement.theorem_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:32:39.376158+00:00
-- url     : https://prove2.me/theorems/dba11d69-fb07-44a5-a128-1ccc9acc3814
-- title:
--   Theorem 3.6, p. 10 — the Fisher Market Mechanism with additive valuations has price of anarchy no better than e^{1/e}
-- statement:
--   For every constant $c<e^{1/e}\approx1.445$ there is an instance with additive valuations $v_{i,j}\ge0$ and budgets $B_i\ge1$, and a feasible allocation $y$, such that for **every** outcome rule $O$ of the Fisher Market Mechanism (Definition 3.1, including the clause that selects an equilibrium preferred by all agents whenever one exists) the induced game has a pure Nash equilibrium $s$ whose outcome $x=x(O(s))$ satisfies
--   $$NSW(x)>0\qquad\text{and}\qquad c\cdot NSW(x)\ \le\ NSW(y).$$
--
--   Hence the price of anarchy of the mechanism, the supremum over instances, is at least $e^{1/e}$, and the upper bound $2$ of Theorem 3.3 cannot be lowered below $e^{1/e}$.
--
--   **Formalization Note** The constant is $e^{1/e}$ exactly, written `Real.exp (1 / Real.exp 1)`. The paper's proof checks deviations with prices held fixed (Lemmas 3.7, 3.8); the statement is the theorem, not that heuristic.
--
--   **Formalization Note** The result is generalized to partial outcome rules. For a source total rule every existence guard holds, so the Nash condition and the stated result specialize to the source claim. No existence of a total rule is asserted.
--
--   Differences from the source:
--   - encoding: the price of anarchy is no better than e^{1/e} (a supremum over instances of maxima of ratios) → for every c < e^{1/e} there are an instance and a feasible y such that every admissible rule has a pure Nash equilibrium x with c·NSW(x) ≤ NSW(y); reason: a supremum is at least e^{1/e} exactly when every smaller c is exceeded; quantifying the instance before the rule is equivalent to the mechanism-level statement because a mechanism chooses its rule independently for each instance
--   - reading: the ratio NSW(x*)/NSW(x) → NSW(x) > 0 is required of the equilibrium; reason: excludes reaching the bound through a zero denominator; the paper's construction has positive NSW
--   - reading: If there exists a market equilibrium E preferred by all the agents (with respect to their true valuations), then E is the outcome → if some equilibrium gives every agent at least its true utility at every other equilibrium, the rule returns an equilibrium with that property; reason: the clause compares E with the alternative equilibria of the same reported market
--   - generalization: Definition 3.1 gives the outcome as a market equilibrium of the reported market and presumes one exists → the separately named IsPartialOutcomeRule returns an equilibrium wherever one exists; IsMechPNE compares deviations to such profiles; reason: every source total rule is a partial rule; for a total rule all admissible profiles (including deviations) have equilibria, so IsMechPNE is exactly the source Nash condition and the entire formal claim specializes to the printed one. The broader class is declared, not treated as an equivalent definition
--   - reading: the outcome is an equilibrium of ⟨B_i, s_i⟩ after removing the goods j with Σ_i s_i(j) = 0 → an equilibrium of the full reported market in which each removed good has price 0 and is held by nobody; reason: the reported utilities ignore removed goods, so these are exactly the equilibria of the reduced market, written on all m goods
--   - reading: optimal bundle: ∀ y with y·p ≤ B_i → ∀ y ≥ 0 with p·y ≤ B_i; reason: bundles are quantities of goods; this is the reading of the published base mission
--   - reading: Nash equilibrium → pure Nash equilibrium; reason: §2 (p. 6) defines the price of anarchy over the set E of pure Nash equilibria
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 10, Theorem 3.6; Definition 3.1, pp. 7–8; construction pp. 10–11

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_3_6 (c : ℝ) (hc : c < Real.exp (1 / Real.exp 1)) :
    ∃ (n m : ℕ) (I : Instance n m), LinStanding I ∧
      ∃ y : Fin n → Fin m → ℝ, Feasible I y ∧
        ∀ O : (Fin n → Fin m → ℝ) → (Fin m → ℝ) × (Fin n → Fin m → ℝ),
          IsPartialOutcomeRule (· ∈ orthant m) (linMechEq I) O →
          SelectsPreferred (· ∈ orthant m) (linMechEq I) (linU I) O →
          ∃ s : Fin n → Fin m → ℝ, IsMechPNE (· ∈ orthant m) (linMechEq I) (linU I) O s ∧
            0 < NSWU I (linU I) (O s).2 ∧
            c * NSWU I (linU I) (O s).2 ≤ NSWU I (linU I) y := by sorry

end TradingPostNSW.Leontief.Supplement
