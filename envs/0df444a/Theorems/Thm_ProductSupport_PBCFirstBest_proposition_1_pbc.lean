-- Prove2me | Theorems.Thm_ProductSupport_PBCFirstBest_proposition_1_pbc
-- name    : ProductSupport.PBCFirstBest.proposition_1_pbc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:29.499915+00:00
-- url     : https://prove2.me/theorems/793bfb4b-20f6-45a4-88c1-5bb0d385b94d
-- title:
--   Proposition 1(ii)–(iii) — first-best PBC rate, payoff, and type ordering
-- statement:
--   For each type $\tau\in\{L,H\}$, the first-best repair rate $\mu^0_\tau=\sqrt{r\lambda_\tau/c}$ maximizes joint profit among positive repair rates. Its joint profit is
--   $$
--   \Pi^0_\tau=r-2\sqrt{cr\lambda_\tau}-c_r\lambda_\tau.
--   $$
--   The low-failure type has the lower first-best repair rate, the higher expected uptime, and the higher joint profit. When its first-best rate exceeds its failure rate and its first-best uptime price $v^0_\tau$ is positive, the resulting contract binds that type's IR constraint and maximizes the supplier's payoff among all positive-price, positive-rate contracts satisfying that IR constraint. These PBC claims give the full-information benchmark used in Proposition 5(i).
--
--   **Formalization Note** The theorem states only the PBC portions of Proposition 1(ii)–(iii); TBC comparisons are outside this mission. The positivity conditions make the paper's strict-price feasible set and the denominator in $v^0_\tau$ explicit.
-- source:
--   Li, Mishra & Netessine, Contracting for Product Support under Information Asymmetry, SSRN 2881356 (author version of Management Science, doi:10.1287/mnsc.2022.4606), p. 12 (PDF 12), Proposition 1(ii)–(iii); supplement pp. 3–4 (PDF 36–37), proof of Proposition 1

import Mathlib
import Definitions.Def_ProductSupport_PBCFirstBest_Model

namespace ProductSupport.PBCFirstBest

theorem proposition_1_pbc (P : Params) (hS : P.Standing) :
    (∀ lam mu : ℝ, (lam = P.lamL ∨ lam = P.lamH) → 0 < mu →
      scProfit P lam mu ≤ Pi0 P lam) ∧
    (∀ lam : ℝ, (lam = P.lamL ∨ lam = P.lamH) →
      Pi0 P lam = P.r - 2 * Real.sqrt (P.c * P.r * lam) - P.cr * lam) ∧
    mu0 P P.lamL < mu0 P P.lamH ∧
    uptime P.lamH (mu0 P P.lamH) < uptime P.lamL (mu0 P P.lamL) ∧
    Pi0 P P.lamH < Pi0 P P.lamL ∧
    (∀ lam M : ℝ, ((lam = P.lamL ∧ M = P.ML) ∨
      (lam = P.lamH ∧ M = P.MH)) → lam < mu0 P lam →
      0 < v0 P lam M →
      custPayoff P lam ⟨v0 P lam M, mu0 P lam⟩ = M ∧
      ∀ k : Contract, 0 < k.v → 0 < k.mu →
        M ≤ custPayoff P lam k →
        suppPayoff P lam k ≤
          suppPayoff P lam ⟨v0 P lam M, mu0 P lam⟩) := by sorry

end ProductSupport.PBCFirstBest
