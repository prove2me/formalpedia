-- Prove2me | Theorems.Thm_PlatformPrecommit_Commission_lemma_4
-- name    : PlatformPrecommit.Commission.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:57.689987+00:00
-- url     : https://prove2.me/theorems/6d8e9b18-fa0b-452d-a29f-bb0cc049f299
-- title:
--   Lemma 4, p. 13 — the unique symmetric selected commission equilibrium and its outcome
-- statement:
--   Let $\Omega>0$ and $0\leq\beta,\gamma<1$. The commission-precommitment game admits a symmetric subgame-perfect equilibrium whose common pay-out ratio is the radical $\alpha^*$ of equation (7). Every symmetric equilibrium under the stated positive-profit subgame selection has that ratio and, for each platform, price and profit
--
--   $$p_i=\frac{\Omega}{1-\gamma+(1-\beta)\alpha^*},\qquad \pi_i=\frac{\alpha^*(1-\beta)(1-\alpha^*)}{(1+\alpha^*-\gamma-\beta\alpha^*)^2}\Omega^2.$$
--
--   These are equations (8) and (9), the commission outcome needed for Proposition 3(b).
--
--   **Formalization Note** “Unique symmetric” restricts only the equilibrium pay-out ratio profile; unilateral first-stage deviations and the second-stage strategy map still cover asymmetric admissible ratios. The strategy map selects a positive-profit price equilibrium whenever one exists, to exclude zero-profit off-path punishments.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), p. 13, Lemma 4, (7)–(9); Online Appendix pp. 30–31, Proof of Lemma 4

import Mathlib
import Definitions.Def_PlatformPrecommit_Commission_AlphaStar

namespace PlatformPrecommit.Commission

/-- Lemma 4: existence and uniqueness among symmetric, selected subgame-perfect equilibria. -/
theorem lemma_4 (M : Model) (hM : M.Standing) :
    (∃ σ : (Fin 2 → ℝ) → (Fin 2 → ℝ),
      IsCSPE M (fun _ => alphaStar M) σ) ∧
    (∀ α σ, IsCSPE M α σ → Symmetric α → ∀ i,
      α i = alphaStar M ∧
      (σ α) i = M.Ω / (1 - M.γ + (1 - M.β) * alphaStar M) ∧
      profC M α (σ α) i =
        alphaStar M * (1 - M.β) * (1 - alphaStar M) /
          (1 + alphaStar M - M.γ - M.β * alphaStar M) ^ 2 * M.Ω ^ 2) := by sorry

end PlatformPrecommit.Commission
