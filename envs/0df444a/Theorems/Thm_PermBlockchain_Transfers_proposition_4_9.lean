-- Prove2me | Theorems.Thm_PermBlockchain_Transfers_proposition_4_9
-- name    : PermBlockchain.Transfers.proposition_4_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:36.831079+00:00
-- url     : https://prove2.me/theorems/84f83bb4-17aa-43cc-8209-9dbc14cea801
-- title:
--   Proposition 4.9, p. 21 — for sufficiently large Δ = H − L, a self-financing system of transfers overcomes adoption failures
-- statement:
--   **Proposition 4.9 (Resolving Adoption Failures).** Fix the model of the Setting, with $L$ held fixed and the horizontal differentiation $\Delta=H-L$ varying. There is $\Delta_0$ such that for every $\Delta>\Delta_0$ there exist an access fee $\kappa$ and transfers $\{\tau_i\}_{i\in M}$ such that
--   1. $\tau_i\ge 0$ for every manufacturer $i$;
--   2. the system is self-financing:
--   $$\kappa\cdot\mu_\kappa=\sum_{i\in M}\tau_i,$$
--   where $\mu_\kappa$ is the probability mass of consumers whose outside option makes paying the fee $\kappa$ optimal;
--   3. full blockchain adoption ($a_i=1$ for every $i$) is an equilibrium of the adoption game in which manufacturer $i$ earns $\Pi(a_i,a_{-i})-\chi_i a_i+\tau_i a_i$.
--
--   In the paper's terms: for sufficiently large $\Delta$, there exists a system of transfers that overcomes adoption failures. Together with Proposition 4.8 it shows that the adoption failure caused by zero manufacturer profits can be undone by moving part of the consumers' information gain to the manufacturers.
--
--   **Formalization Note** The statement is in the reduced form of the paper's own proof (pp. 36–38): consumer utilities from Proposition A.1's full-adoption outcome, gross profit $\Pi\equiv 0$, and equilibrium as a pure Nash equilibrium over unilateral switches of $a_i\in\{0,1\}$. The mass $\mu_\kappa$ is not a free parameter but the $\mu$-measure of the outside-option values for which paying is optimal (ties resolved towards paying). The fee $\kappa$ carries no sign constraint, as on p. 20; for $\Delta\ge 0$ a negative fee cannot satisfy the statement, because then every consumer pays and $\kappa=\sum_i\tau_i\ge\sum_i\chi_i>0$ would be required.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), p. 21, Proposition 4.9; definitions (14)–(16), pp. 20–21

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Setting

namespace PermBlockchain.Transfers
theorem proposition_4_9 {m : ℕ} (M : Model m) (hM : M.Standing) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → ∃ (κ : ℝ) (τ : Mfr m → ℝ), M.Overcomes Δ κ τ := by sorry
end PermBlockchain.Transfers
