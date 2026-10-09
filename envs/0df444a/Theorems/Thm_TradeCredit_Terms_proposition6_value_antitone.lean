-- Prove2me | Theorems.Thm_TradeCredit_Terms_proposition6_value_antitone
-- name    : TradeCredit.Terms.proposition6_value_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:11:44.786336+00:00
-- url     : https://prove2.me/theorems/fe6593f1-d3b2-4067-af2f-1dac3b77e376
-- title:
--   Proposition 6 (first sentence), p. 21 — the supplier's optimal profit Π*_s decreases in α_b and in α_t
-- statement:
--   Let the demand density $f$ satisfy the standing assumptions of §3, and let $0<c<1$ and $K>0$. Write $\Theta_{\alpha_b}$ for the threshold domain, $\Pi_s(\cdot;\alpha_b,\alpha_t)$ for the supplier's profit (8), and
--   $$\Pi_s^*(\alpha_b,\alpha_t)=\sup_{(\theta_b,\theta_t)\in\Theta_{\alpha_b}}\Pi_s(\theta_b,\theta_t;\alpha_b,\alpha_t)$$
--   for her optimal profit. Then:
--   1. **In $\alpha_b$.** For $\alpha_t\in[0,1]$ and $0\le a\le a'\le 1$, every $(\theta_b,\theta_t)\in\Theta_{a'}$ satisfies $\Pi_s(\theta_b,\theta_t;a',\alpha_t)\le\Pi_s^*(a,\alpha_t)$.
--   2. **In $\alpha_t$.** For $\alpha_b\in[0,1]$ and $0\le a\le a'\le 1$, every $(\theta_b,\theta_t)\in\Theta_{\alpha_b}$ satisfies $\Pi_s(\theta_b,\theta_t;\alpha_b,a')\le\Pi_s^*(\alpha_b,a)$.
--
--   When $\Theta_{a'}$ is nonempty, each part says exactly that $\Pi_s^*(a')\le\Pi_s^*(a)$: the supplier's optimal profit (weakly) decreases in both deadweight cost proportions. The $\alpha_b$ part is used in the proof of Proposition 3 to pass from $\alpha_b=0$ to general $\alpha_b$.
--
--   **Formalization Note** Only the unconditional first sentence of Proposition 6 is formalized. Parts 1–2 assume that the conditions of Lemma 1 are sufficient for global optimality and are not stated. The monotonicity is weak, as in the proof (p. 41: "(weakly) decreases in $\alpha_b$"). The domain $\Theta$ depends on $\alpha_b$, and each supremum is over that parameter's own domain. In Lean, `sSup` of an empty or unbounded set is $0$. The statement compares each attained value at the larger parameter with the supremum at the smaller one, so it never reads $\Pi_s^*$ at an empty domain. $\Pi_s$ is bounded above on $\Theta$, so this supremum is a true supremum.
-- source:
--   Yang & Birge, Trade Credit, Risk Sharing, and Inventory Financing Portfolios, Management Science 64(8) (2018), accepted manuscript (LBS Research Online eprint 801), p. 21, Proposition 6 (first sentence); proof p. 41

import Mathlib
import Definitions.Def_TradeCredit_Terms_Model

namespace TradeCredit.Terms

theorem proposition6_value_antitone (f : ℝ → ℝ) (hf : DemandModel f)
    (c K : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hK : 0 < K) :
    (∀ αt : ℝ, 0 ≤ αt → αt ≤ 1 → ∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ 1 →
        ∀ p ∈ Theta f c a' K, PiS f c a' αt K p.1 p.2 ≤ PiSstar f c a αt K) ∧
      (∀ αb : ℝ, 0 ≤ αb → αb ≤ 1 → ∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ 1 →
        ∀ p ∈ Theta f c αb K, PiS f c αb a' K p.1 p.2 ≤ PiSstar f c αb a K) := by sorry

end TradeCredit.Terms
