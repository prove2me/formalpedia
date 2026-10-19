-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_theorem_3
-- name    : SupplyFlex.SupplierLed.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:53.793955+00:00
-- url     : https://prove2.me/theorems/01165029-0baa-4158-a723-a0184ba2dbb6
-- title:
--   Theorem 3, p. 10 (corrected: outcome unique only away from the Scenario 2/3 tie; β̄ not claimed unique) — the supply-flexibility equilibrium
-- statement:
--   Consider the supply-flexibility game of a standard model, with $\tilde q$, $q^o$, $\hat q^*$, $\check q$ the solutions of (1)–(4) as in the Setting ($\tilde q$ when $c + (1-p)s \le r$, $\hat q^* = 0$ when $s > r$, $\check q \ge \hat q^*$ when $w^o > s$), and $\kappa^*$, $\bar\beta^*$, $w^*$ the closed forms of p. 10:
--   $$\bar\beta^* = \begin{cases} 0 & s > r,\\ 1 & s \le r,\ s < w^o,\ \check q(ps - c) < \tilde q\bigl(r\bar F(\tilde q) - (1-p)s - c\bigr),\\ \hat q^*/\kappa^* & \text{otherwise,}\end{cases} \qquad w^* = \frac{r\bigl[p\bar F(\kappa^*) + (1-p)\bar\beta^*\bar F(\bar\beta^*\kappa^*)\bigr]}{p + (1-p)\bar\beta^*}.$$
--   Then:
--   1. there is a subgame-perfect equilibrium with wholesale price $w^*$, guaranteed fraction $\bar\beta^*$, order $q = \kappa^*$, input $y = \kappa^*$, and delivery $z = \kappa^* \max\{\alpha, \bar\beta^*\}$ for $\alpha \in \{0, 1\}$;
--   2. unless $w^o > s$ and $\check q(ps - c) = \tilde q\bigl(r\bar F(\tilde q) - (1-p)s - c\bigr)$, every subgame-perfect equilibrium has price $w^*$, order $\kappa^*$, input $\kappa^*$, and delivery $\kappa^*\max\{\alpha, \bar\beta^*\}$ for each outcome $\alpha$ of positive probability.
--
--   This is the equilibrium of the supply-flexibility contract against which Theorem 6 compares the price-only equilibrium of Theorem 2.
--
--   **Formalization Note.** The paper states this equilibrium as unique. Three corrections: when the supplier sets $w > s$ (Scenario 3) or $p = 1$, the guaranteed fraction does not affect the outcome, so $\bar\beta$ itself is not claimed unique; at the tie of Scenarios 2 and 3 both outcomes are equilibria, so uniqueness is claimed only away from it; and at $p = 1$ the delivery is claimed only for $\alpha = 1$. The roots are arguments with hypotheses saying they solve (1)–(4).
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), p. 10, Theorem 3, eqs. (1)–(4), w°, κ*; restated App. A2 p. 6 (PDF 45)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Theorem 3, p. 10 (restated App. A2 p. 6, PDF 45) (corrected: the equilibrium outcome is
unique away from the tie of Scenarios 2–3, and `β̄` itself is not claimed unique). -/
theorem theorem_3 (M : Model) (hM : M.Std) (qt qo qh qc : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hqc : M.s < wo M qo qh → qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh)) :
    (∃ σ : Profile, IsSPE M .flex σ ∧ σ.w = wStar M qt qo qh qc ∧
        σ.b = betaStar M qt qo qh qc ∧
        σ.Q σ.w σ.b = kappaStar M qt qo qh qc ∧
        σ.Y σ.w σ.b (kappaStar M qt qo qh qc) = kappaStar M qt qo qh qc ∧
        ∀ α : Bool, σ.Z σ.w σ.b (kappaStar M qt qo qh qc) (kappaStar M qt qo qh qc) α =
          kappaStar M qt qo qh qc * max (if α then 1 else 0) (betaStar M qt qo qh qc)) ∧
    (¬ (M.s < wo M qo qh ∧
        qc * (M.p * M.s - M.c) = qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)) →
      ∀ σ : Profile, IsSPE M .flex σ →
        σ.w = wStar M qt qo qh qc ∧
        σ.Q σ.w σ.b = kappaStar M qt qo qh qc ∧
        σ.Y σ.w σ.b (kappaStar M qt qo qh qc) = kappaStar M qt qo qh qc ∧
        ∀ α : Bool, (α = true ∨ M.p < 1) →
          σ.Z σ.w σ.b (kappaStar M qt qo qh qc) (kappaStar M qt qo qh qc) α =
            kappaStar M qt qo qh qc * max (if α then 1 else 0) (betaStar M qt qo qh qc)) := by sorry

end SupplyFlex.SupplierLed
