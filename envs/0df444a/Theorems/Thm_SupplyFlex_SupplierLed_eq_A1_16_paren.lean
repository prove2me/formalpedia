-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_eq_A1_16_paren
-- name    : SupplyFlex.SupplierLed.eq_A1_16_paren
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T05:37:58.560335+00:00
-- url     : https://prove2.me/theorems/a5fb11b6-a373-4254-b875-2a76b1b2be04
-- title:
--   (A1.16), proof of Theorem 6, App. A1 p. 4 (PDF 36), parenthesised — $p\int_0^{q^o}xf+(1-p)\int_0^{\hat q^*}xf\ge\int_0^{\tilde q}xf$
-- statement:
--   In a standard model whose demand density $f$ is log-concave, suppose $s\le r$. Let $\tilde q$, $q^o$, $\hat q^*$ be the solutions in $[0,\infty)$ of (1), (2), (3):
--   $$rG(\tilde q)=c+(1-p)s,\qquad rpG(q^o)=c,\qquad rG(\hat q^*)=s.$$
--   Then
--   $$p\int_0^{q^o}xf(x)\,dx+(1-p)\int_0^{\hat q^*}xf(x)\,dx-\int_0^{\tilde q}xf(x)\,dx\ \ge\ 0.\qquad\text{(A1.16)}$$
--
--   The buyer's equilibrium profit is $r$ times the truncated mean $\int_0^q xf$ at the delivered quantity. So this is the buyer's half of Theorem 6 in the case $s\le r$, $\kappa^*=q^o$.
--
--   **Formalization Note.** This restates the milestone `SupplyFlex.SupplierLed.eq_A1_16` with parentheses around the first integral on the right. Lean's `∫ x in s, body` notation swallows the following `+ (1 - p) * ∫ ...` into its body, so the milestone's right side reads $p\int_0^{q^o}\bigl(xf(x)+(1-p)\int_0^{\hat q^*}yf\bigr)dx$. That version is false and has been disproved (uniform demand on $[0,1)$). $\int_0^q$ is the integral over $(0,q]$. Log-concavity is `ConvexOptimization.LogConcaveOn` on all of $\mathbb R$.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break: sharing supply risk using the supply-flexibility contract (SSRN 3143238; M&SOM 23(5) 2021), p. 13 Theorem 6; proof App. A1 p. 4 (PDF 36), eq. (A1.16)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_LogConcaveOn
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- (A1.16), proof of Theorem 6, App. A1 p. 4 (PDF 36), with the first integral parenthesised:
for log-concave demand and `s ≤ r`, `∫₀^{q̃} x f ≤ p ∫₀^{q°} x f + (1 − p) ∫₀^{q̂*} x f`. -/
theorem eq_A1_16_paren (M : Model) (hM : M.Std)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ M.f) (qt qo qh : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hsr : M.s ≤ M.r) :
    (∫ x in Set.Ioc 0 qt, x * M.f x) ≤
      M.p * (∫ x in Set.Ioc 0 qo, x * M.f x) + (1 - M.p) * ∫ x in Set.Ioc 0 qh, x * M.f x := by
  sorry

end SupplyFlex.SupplierLed
