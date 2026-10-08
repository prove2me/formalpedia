-- Prove2me | Theorems.Thm_RevenueOrdered_UDPmin_exists_optimal_valuation_prices
-- name    : RevenueOrdered.UDPmin.exists_optimal_valuation_prices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:09.955648+00:00
-- url     : https://prove2.me/theorems/df0c083b-1741-4199-bc67-f38ee8aa831d
-- title:
--   Lemma 4.5 — some optimal $\mathrm{UDP}_{\min}$ price assignment uses only valuations as prices
-- statement:
--   Consider a $\mathrm{UDP}_{\min}$ instance with items $[n]$, at least one consumer, interest sets $B_i$ and valuations $v_1,\dots,v_m>0$. Then there is a price assignment $p$ with
--   $$p(x)\in\{v_1,\dots,v_m\}\quad\text{for all } x\in[n]$$
--   that is optimal: $\mathrm{rev}_{\mathrm{UDP}}(p')\le\mathrm{rev}_{\mathrm{UDP}}(p)$ for every positive price assignment $p'$, and $\mathrm{rev}_{\mathrm{UDP}}(p)=\mathrm{OPT}_{\mathrm{UDP}}$. In particular the supremum defining $\mathrm{OPT}_{\mathrm{UDP}}$ is attained.
--
--   The lemma reduces the uncountable search over prices to a finite one; it is what makes the assortment instance of Theorem 4.6 reach the pricing optimum.
--
--   **Formalization Note** The price $p$ is positive because valuations are. The paper's proof starts from an optimal assignment; here its existence is part of the statement.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 17, Lemma 4.5 (proof in Appendix B, p. 30)

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Pricing

namespace RevenueOrdered.UDPmin

/-- Lemma 4.5 (Berbeglia–Joret, arXiv:1606.01371v3, p. 17; proof in App. B, p. 30): some optimal
price assignment takes only valuations as prices. -/
theorem exists_optimal_valuation_prices {X M : Type*} [Fintype X] [Fintype M] [Nonempty M]
    (I : Instance X M) :
    ∃ p : X → ℝ, (∀ x, ∃ i, p x = I.v i) ∧
      (∀ p' : X → ℝ, (∀ x, 0 < p' x) → revenue I p' ≤ revenue I p) ∧
      revenue I p = optUDP I := by sorry

end RevenueOrdered.UDPmin
