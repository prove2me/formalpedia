-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_3_9
-- name    : TradingPostNSW.Leontief.Supplement.theorem_3_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:33:31.006147+00:00
-- url     : https://prove2.me/theorems/4c44806f-4b97-4fd1-ba4f-f3dcf0063e0a
-- title:
--   Theorem 3.9, p. 11 — the Fisher Market Mechanism with Leontief valuations has price of anarchy n, and the bound is tight
-- statement:
--   Consider the Fisher Market Mechanism (Definition 3.1) with Leontief valuations: agent $i$ has utility $u_i(x_i)=\min_{j:v_{i,j}>0}x_{i,j}/v_{i,j}$ and budget $B_i\ge1$, reports a Leontief vector $s_i\in\mathbb R^m_{\ge0}$, and the outcome is a market equilibrium of the reported Leontief market (goods nobody reports removed).
--
--   1. **Upper bound.** For every instance, every outcome rule $O$ returning such an equilibrium, every pure Nash equilibrium $s$ and every feasible allocation $y$,
--   $$NSW(y)\ \le\ n\cdot NSW\big(x(O(s))\big).$$
--   2. **Tightness.** For every $n\ge1$ there are an $n$-agent Leontief instance and a feasible $y$ such that every outcome rule satisfying Definition 3.1 (including the selection clause) has a pure Nash equilibrium $s$ with $NSW(x(O(s)))>0$ and
--   $$NSW(y)= n\cdot NSW\big(x(O(s))\big).$$
--
--   Thus misreporting can cost a factor equal to the number of agents for perfect complements, in contrast with the constant factor for substitutes (Theorem 3.3).
--
--   **Formalization Note** Tightness rests in the paper on Lemma A.1 (cited from Brânzei et al. 2014, not proved in this paper); only its instance with uniform reports is needed.
--
--   **Formalization Note** The result is generalized to partial outcome rules. For a source total rule every existence guard holds, so the Nash condition and the stated result specialize to the source claim. No existence of a total rule is asserted.
--
--   Differences from the source:
--   - encoding: price of anarchy at most c (a maximum of ratios NSW(x*)/NSW(x)) → NSW(y) ≤ c·NSW(x) for every feasible y and every equilibrium outcome x; reason: the multiplicative form avoids dividing by NSW(x); it is the ratio bound with a/0 = ∞
--   - reading: the bound is tight → for every n ≥ 1 an instance, a feasible y and, for every rule of Definition 3.1, a pure Nash equilibrium with NSW(y) = n·NSW(x) > 0; reason: tightness of a worst-case ratio means it is attained; positivity excludes a zero denominator; the instance of p. 20 is the intended witness
--   - reading: the selection clause of Definition 3.1 → an equilibrium weakly preferred by every agent to every other equilibrium is returned when one exists; reason: the clause compares E with the alternative equilibria of the same reported market
--   - reading: a report s_i ∈ ℝ^m_{≥0}, including s_i = 0 → the reported Leontief utility of s_i = 0 is 0 (the base convention for an agent demanding no good); reason: the minimum over an empty set of goods is undefined on the page
--   - generalization: Definition 3.1 gives the outcome as a market equilibrium of the reported market and presumes one exists → the separately named IsPartialOutcomeRule returns an equilibrium wherever one exists; IsMechPNE compares deviations to such profiles; reason: every source total rule is a partial rule; for a total rule all admissible profiles (including deviations) have equilibria, so IsMechPNE is exactly the source Nash condition and the entire formal claim specializes to the printed one. The broader class is declared, not treated as an equivalent definition
--   - reading: the outcome is an equilibrium of ⟨B_i, s_i⟩ after removing the goods j with Σ_i s_i(j) = 0 → an equilibrium of the full reported market in which each removed good has price 0 and is held by nobody; reason: the reported utilities ignore removed goods, so these are exactly the equilibria of the reduced market, written on all m goods
--   - reading: optimal bundle: ∀ y with y·p ≤ B_i → ∀ y ≥ 0 with p·y ≤ B_i; reason: bundles are quantities of goods; this is the reading of the published base mission
--   - reading: Nash equilibrium → pure Nash equilibrium; reason: §2 (p. 6) defines the price of anarchy over the set E of pure Nash equilibria
--   - encoding: Leontief utilities need demanded goods → the base standing assumption: m ≥ 1, v ≥ 0, B_i ≥ 1 and every agent demands a good; reason: the minimum defining u_i is over a nonempty set; this is the published base convention
--   - generalization: the upper bound for the Fisher Market Mechanism of Definition 3.1, including its preferred-equilibrium selection clause → the upper-bound conjunct allows every partial equilibrium-valued rule, without SelectsPreferred; the tightness conjunct retains SelectsPreferred; reason: dropping the selection premise enlarges the upper-bound domain; every source rule is included, and the full factor n conclusion specializes to it
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 11, Theorem 3.9; proof and instance p. 20 (Appendix A)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_3_9 :
    (∀ (n m : ℕ) (I : Instance n m), Standing I →
      ∀ O : (Fin n → Fin m → ℝ) → (Fin m → ℝ) × (Fin n → Fin m → ℝ),
        IsPartialOutcomeRule (· ∈ orthant m) (leoMechEq I) O →
        ∀ s : Fin n → Fin m → ℝ, IsMechPNE (· ∈ orthant m) (leoMechEq I) (u I) O s →
          ∀ y : Fin n → Fin m → ℝ, Feasible I y → NSW I y ≤ (n : ℝ) * NSW I (O s).2) ∧
    (∀ n : ℕ, 0 < n → ∃ (m : ℕ) (I : Instance n m), Standing I ∧
      ∃ y : Fin n → Fin m → ℝ, Feasible I y ∧
        ∀ O : (Fin n → Fin m → ℝ) → (Fin m → ℝ) × (Fin n → Fin m → ℝ),
          IsPartialOutcomeRule (· ∈ orthant m) (leoMechEq I) O →
          SelectsPreferred (· ∈ orthant m) (leoMechEq I) (u I) O →
          ∃ s : Fin n → Fin m → ℝ, IsMechPNE (· ∈ orthant m) (leoMechEq I) (u I) O s ∧
            0 < NSW I (O s).2 ∧ NSW I y = (n : ℝ) * NSW I (O s).2) := by sorry

end TradingPostNSW.Leontief.Supplement
