-- Prove2me | Theorems.Thm_PlatformPrecommit_KS_proposition_1
-- name    : PlatformPrecommit.KS.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:41.913203+00:00
-- url     : https://prove2.me/theorems/38ff1a30-b1e9-4021-83a8-a17a1118479a
-- title:
--   Proposition 1, p. 15 — generalized Kreps–Scheinkman equivalency
-- statement:
--   Consider the two-platform market with $\Omega>0$ and $0\le\beta,\gamma<1$. A subgame-perfect equilibrium of the two-stage capacity game exists, as does a Nash equilibrium of the single-stage quantity game. For every such pair of equilibria and each platform $i$, the second-stage price, wage, number of matches, and profit under capacity precommitment equal the respective outcomes of quantity competition:
--
--   $$p_i^{\mathrm{capacity}}=p_i^{\mathrm{quantity}},\qquad w_i^{\mathrm{capacity}}=w_i^{\mathrm{quantity}},\qquad m_i^{\mathrm{capacity}}=z_i^{\mathrm{quantity}},\qquad \pi_i^{\mathrm{capacity}}=\pi_i^{\mathrm{quantity}}.$$
--
--   This establishes the two-sided counterpart of capacity-then-price versus quantity competition, with wages and service-provider supply included.
--
--   **Formalization Note** Each continuation of the two-stage equilibrium is a price-and-wage Nash equilibrium and selects positive profit for each platform whenever some subgame equilibrium permits it. This added selection excludes zero-profit off-path punishment equilibria that would invalidate the unqualified printed claim. Both existence assertions are explicit, so the universal outcome equality is not vacuous. Quantity outcomes come from actual equilibria, not from closed forms built into a definition.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), p. 15, Proposition 1; Online Appendix p. 33, proof of Proposition 1

import Mathlib
import Definitions.Def_PlatformPrecommit_KS_Setting

namespace PlatformPrecommit.KS

/-- Proposition 1, p. 15: generalized Kreps–Scheinkman equivalency. -/
theorem proposition_1 (M : Model) (hM : M.Standing) :
    (∃ q σ, M.IsSPE q σ) ∧ (∃ z, M.IsQNE z) ∧
    ∀ q σ z, M.IsSPE q σ → M.IsQNE z → ∀ i : Fin 2,
      (σ q).1 i = M.qPrice z i ∧ (σ q).2 i = M.qWage z i ∧
      M.ksMatch q (σ q) i = z i ∧ M.ksProfit q (σ q) i = M.qProfit z i := by sorry

end PlatformPrecommit.KS
