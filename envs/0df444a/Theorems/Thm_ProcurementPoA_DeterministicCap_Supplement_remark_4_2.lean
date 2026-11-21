-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_remark_4_2
-- name    : ProcurementPoA.DeterministicCap.Supplement.remark_4_2
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-20T16:29:42.194429+00:00
-- url     : https://prove2.me/theorems/2d9c315d-a297-4bf1-ba79-68edf56e0b81
-- title:
--   Remark 4.2 — the bound of Theorem 4.1 is tight
-- statement:
--   **Source.** Remark 4.2 (p. 7): "The bound in Theorem 4.1 is tight." The paper takes the worst-case instances of the first-price value auction of Jin and Lu [JL23a, Example 4, Section 6] ([doi:10.1145/3617902](https://doi.org/10.1145/3617902)), rescaled so that values and equilibrium bids lie in $[0,1]$, with $\mathbb{E}[v^\star_n] \to 1$ and $\mathbb{E}[v^{\mathrm{eq}}_n] \to 1 - 1/e^2$ by their Lemmas 6.1 and 6.2. It maps them to procurement instances by $c_i = \bar c - A v_i$ and $b^P_i = \bar c - A b^V_i$ with $A = \bar c - \underline c$, so that $\mathbb{E}[c^{\mathrm{eq}}_n]/\mathbb{E}[c^\star_n] \to 1 + \frac{1}{e^2}\big(\frac{\bar c}{\underline c} - 1\big)$, "approached by instances with finitely many bidders".
--
--   **Statement.** For all reals $0 < L \le U$ and every $\delta > 0$ there is an instance of the first-price procurement auction of Theorem 4.1 with ratio within $\delta$ of $1 + e^{-2}(U/L - 1)$. That is, there are:
--   - finitely many suppliers ($n+1$) with independent costs whose possible values lie in $[L,U]$;
--   - a measurable tie rule $\tau$ selecting a lowest bidder;
--   - a mixed profile $\sigma$.
--
--   The profile is an equilibrium with bids restricted to $[L,U]$ (`ProcurementPoA.DeterministicCap.Supplement.IsBidSetBNE` with $A = [L,U]$, as in the mission's Theorem 4.1): no bid below cost, every bid used lies in $[L,U]$, and it is a best response among bids in $[L,U]$. Its ratio of the expected winner's cost (`standardSocialCost`) to the expected lowest cost (`optimalSocialCost`) is at least $1 + e^{-2}(U/L - 1) - \delta$. Here $\varepsilon = e^{-2}$ is `ProcurementPoA.DeterministicCap.epsilon`.
--
--   **Role.** This is the lower half of Theorem 5.3. With $L = 1$ and $U = T$, these instances are equilibria of the deterministic cap $T$, so the price of anarchy of $\mathcal M_T$ is at least $1 + \varepsilon(T-1)$.
-- source:
--   S. Palazzotto and A. Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission 293, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, p. 7, Remark 4.2, citing Jin and Lu [JL23a, Example 4 and Lemmas 6.1, 6.2]

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open MeasureTheory

namespace ProcurementPoA.DeterministicCap.Supplement

theorem remark_4_2 (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n),
      InCostInterval D L U ∧ IsBidSetBNE D τ σ (Set.Icc L U) ∧
      ENNReal.ofReal (1 + epsilon * (U / L - 1) - δ) ≤
        standardSocialCost D τ σ / optimalSocialCost D := by sorry

end ProcurementPoA.DeterministicCap.Supplement
