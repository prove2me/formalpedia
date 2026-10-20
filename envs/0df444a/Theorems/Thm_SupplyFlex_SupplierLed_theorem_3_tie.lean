-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_theorem_3_tie
-- name    : SupplyFlex.SupplierLed.theorem_3_tie
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-20T05:37:52.13198+00:00
-- url     : https://prove2.me/theorems/f4238cef-8197-4356-853d-cebb0568c5de
-- title:
--   Theorem 3, p. 10, at the Scenario 2/3 tie — every supply-flexibility equilibrium has the Scenario 2 or the Scenario 3 outcome
-- statement:
--   Consider the supply-flexibility game of a standard model. Let $\tilde q,q^o,\hat q^*,\check q$ be the solutions of (1)–(4), and let $\kappa^*$, $\bar\beta^*$, $w^*$ be the closed forms of Theorem 3 (p. 10). Suppose we are at the tie between Scenarios 2 and 3, which the corrected milestone Theorem 3 excludes from its uniqueness claim:
--   $$w^o>s\qquad\text{and}\qquad \check q\,(ps-c)=\tilde q\bigl(r\bar F(\tilde q)-(1-p)s-c\bigr).$$
--   Here $\kappa^*=\check q$ and $\bar\beta^*=\hat q^*/\check q$. Then every subgame-perfect equilibrium $\sigma$, with on-path contract $(w,\bar\beta)$, has one of two outcomes:
--   1. **Scenario 2:** price $w=w^*$, order $q=\kappa^*$, input $y=\kappa^*$, and delivery $z=\kappa^*\max\{\alpha,\bar\beta^*\}$ for every disruption outcome $\alpha$ of positive probability.
--   2. **Scenario 3:** price $w=r\bar F(\tilde q)$, order $q=\tilde q$, input $y=\tilde q$, and delivery $z=\tilde q$ for every disruption outcome of positive probability.
--
--   At the tie the supplier is indifferent between inducing $\check q$ with price $s$ and inducing the price-only outcome $\tilde q$ with full delivery. The proof of Theorem 3 (App. A2) shows these are the only optimal contracts, so the equilibrium outcome is one of the two. Theorem 6 needs this to compare the buyer's profits in every equilibrium.
--
--   **Formalization Note.** Same setting, hypotheses and conventions as the milestone `SupplyFlex.SupplierLed.theorem_3`. "Positive probability" means $\alpha=1$, or $\alpha=0$ when $p<1$. The guaranteed fraction is not claimed unique.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break: sharing supply risk using the supply-flexibility contract (SSRN 3143238; M&SOM 23(5) 2021), Theorem 3 p. 10 and its proof App. A2 pp. 4–6 (PDF 43–45), Scenarios 2 and 3; the tie case left out of the corrected milestone theorem_3

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Theorem 3, p. 10, at the tie of Scenarios 2 and 3 (`w° > s` and
`q̌(ps − c) = q̃(r F̄(q̃) − (1 − p)s − c)`): every equilibrium has the Scenario 2 outcome
(price `w*`, order and input `κ* = q̌`, delivery `κ* max{α, β̄*}`) or the Scenario 3 outcome
(price `r F̄(q̃)`, order, input and delivery `q̃`). -/
theorem theorem_3_tie (M : Model) (hM : M.Std) (qt qo qh qc : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hqc : M.s < wo M qo qh → qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh))
    (htie : M.s < wo M qo qh ∧
        qc * (M.p * M.s - M.c) = qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)) :
    ∀ σ : Profile, IsSPE M .flex σ →
      (σ.w = wStar M qt qo qh qc ∧
        σ.Q σ.w σ.b = kappaStar M qt qo qh qc ∧
        σ.Y σ.w σ.b (kappaStar M qt qo qh qc) = kappaStar M qt qo qh qc ∧
        ∀ α : Bool, (α = true ∨ M.p < 1) →
          σ.Z σ.w σ.b (kappaStar M qt qo qh qc) (kappaStar M qt qo qh qc) α =
            kappaStar M qt qo qh qc * max (if α then 1 else 0) (betaStar M qt qo qh qc)) ∨
      (σ.w = M.r * Fbar M.f qt ∧
        σ.Q σ.w σ.b = qt ∧
        σ.Y σ.w σ.b qt = qt ∧
        ∀ α : Bool, (α = true ∨ M.p < 1) → σ.Z σ.w σ.b qt qt α = qt) := by sorry

end SupplyFlex.SupplierLed
