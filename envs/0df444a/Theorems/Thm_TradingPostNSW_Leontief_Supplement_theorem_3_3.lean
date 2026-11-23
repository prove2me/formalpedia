-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_3_3
-- name    : TradingPostNSW.Leontief.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:31:32.839045+00:00
-- url     : https://prove2.me/theorems/418e1224-0aab-4e39-9a24-df2f1b8b2c11
-- title:
--   Theorem 3.3, p. 8 — the Fisher Market Mechanism with linear valuations has price of anarchy at most 2
-- statement:
--   Let $n$ agents with linear valuations $u_i(y)=\sum_j v_{i,j}y_j$ ($v_{i,j}\ge0$) and budgets $B_i\ge1$ face the **Fisher Market Mechanism** (Definition 3.1): every agent reports a vector $s_i\in\mathbb R^m_{\ge0}$, and the outcome is a market equilibrium of the reported linear market, after removing the goods nobody reports. Fix any outcome rule $O$ returning such an equilibrium, and let $s$ be a pure Nash equilibrium of the induced game, with outcome allocation $x=x(O(s))$. Then for every feasible allocation $y$,
--   $$NSW(y)\ \le\ 2\,NSW(x),\qquad NSW(z)=\Big(\prod_i u_i(z_i)^{B_i}\Big)^{1/B}.$$
--
--   So strategic misreporting in the Fisher market loses at most a factor $2$ of the optimal Nash social welfare.
--
--   **Formalization Note** Lemma 3.4, used by the proof, is false when some other agent reports the zero vector (see that milestone); the theorem is stated at full strength for every report profile and is not weakened to avoid that case.
--
--   **Formalization Note** The result is generalized to partial outcome rules. For a source total rule every existence guard holds, so the Nash condition and the stated result specialize to the source claim. No existence of a total rule is asserted.
--
--   Differences from the source:
--   - encoding: price of anarchy at most c (a maximum of ratios NSW(x*)/NSW(x)) → NSW(y) ≤ c·NSW(x) for every feasible y and every equilibrium outcome x; reason: the multiplicative form avoids dividing by NSW(x); it is the ratio bound with a/0 = ∞
--   - generalization: the outcome rule of Definition 3.1, including its clause selecting an equilibrium preferred by all agents → every outcome rule that returns an equilibrium of the reported market; reason: the bound does not use the selection clause; every rule of Definition 3.1 is such a rule, so the statement specializes to the paper's
--   - generalization: Definition 3.1 gives the outcome as a market equilibrium of the reported market and presumes one exists → the separately named IsPartialOutcomeRule returns an equilibrium wherever one exists; IsMechPNE compares deviations to such profiles; reason: every source total rule is a partial rule; for a total rule all admissible profiles (including deviations) have equilibria, so IsMechPNE is exactly the source Nash condition and the entire formal claim specializes to the printed one. The broader class is declared, not treated as an equivalent definition
--   - reading: the outcome is an equilibrium of ⟨B_i, s_i⟩ after removing the goods j with Σ_i s_i(j) = 0 → an equilibrium of the full reported market in which each removed good has price 0 and is held by nobody; reason: the reported utilities ignore removed goods, so these are exactly the equilibria of the reduced market, written on all m goods
--   - reading: optimal bundle: ∀ y with y·p ≤ B_i → ∀ y ≥ 0 with p·y ≤ B_i; reason: bundles are quantities of goods; this is the reading of the published base mission
--   - reading: Nash equilibrium → pure Nash equilibrium; reason: §2 (p. 6) defines the price of anarchy over the set E of pure Nash equilibria
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 8, Theorem 3.3; Definition 3.1, p. 7; proof pp. 9–10

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_3_3 {n m : ℕ} (I : Instance n m) (hI : LinStanding I)
    (O : (Fin n → Fin m → ℝ) → (Fin m → ℝ) × (Fin n → Fin m → ℝ))
    (hO : IsPartialOutcomeRule (· ∈ orthant m) (linMechEq I) O)
    (s : Fin n → Fin m → ℝ) (hs : IsMechPNE (· ∈ orthant m) (linMechEq I) (linU I) O s)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    NSWU I (linU I) y ≤ 2 * NSWU I (linU I) (O s).2 := by sorry

end TradingPostNSW.Leontief.Supplement
