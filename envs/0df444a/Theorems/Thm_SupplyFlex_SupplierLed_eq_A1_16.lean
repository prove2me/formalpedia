-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_eq_A1_16
-- name    : SupplyFlex.SupplierLed.eq_A1_16
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:58.323286+00:00
-- url     : https://prove2.me/theorems/7c1ab691-6dbc-4aab-bfee-0e546d2d1e9d
-- title:
--   (A1.16), proof of Theorem 6, App. A1 p. 4 (PDF 36) — for log-concave f and s ≤ r, p∫₀^{q°}xf + (1−p)∫₀^{q̂*}xf ≥ ∫₀^{q̃}xf
-- statement:
--   In a standard model whose demand density $f$ is log-concave, suppose $s \le r$, and let $\tilde q$, $q^o$, $\hat q^*$ be the solutions in $[0, \infty)$ of (1), (2), (3). Then
--   $$p\int_0^{q^o} x f(x)\,dx + (1-p)\int_0^{\hat q^*} x f(x)\,dx - \int_0^{\tilde q} x f(x)\,dx \ge 0. \qquad (A1.16)$$
--
--   Since the buyer's equilibrium profit equals $r$ times the truncated mean $\int_0^q x f(x)\,dx$ at the quantity delivered, this is the buyer's half of Theorem 6 in the case $s \le r$, $\kappa^* = q^o$: the buyer's profit under the flexibility contract is at least that under the price-only contract.
--
--   **Formalization Note.** $\int_0^q$ is the integral over $(0, q]$. Log-concavity is the published `ConvexOptimization.LogConcaveOn` on all of $\mathbb R$, in the form that allows $f$ to vanish off $[0, \bar a)$.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), App. A1 p. 4 (PDF 36), proof of Theorem 6, (A1.14)–(A1.16)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_LogConcaveOn
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- (A1.16), proof of Theorem 6, App. A1 p. 4 (PDF 36): for log-concave demand and `s ≤ r`,
`p ∫₀^{q°} x f + (1 − p) ∫₀^{q̂*} x f − ∫₀^{q̃} x f ≥ 0`. -/
theorem eq_A1_16 (M : Model) (hM : M.Std) (hlc : ConvexOptimization.LogConcaveOn Set.univ M.f)
    (qt qo qh : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hsr : M.s ≤ M.r) :
    ∫ x in Set.Ioc 0 qt, x * M.f x ≤
      M.p * ∫ x in Set.Ioc 0 qo, x * M.f x + (1 - M.p) * ∫ x in Set.Ioc 0 qh, x * M.f x := by sorry

end SupplyFlex.SupplierLed
