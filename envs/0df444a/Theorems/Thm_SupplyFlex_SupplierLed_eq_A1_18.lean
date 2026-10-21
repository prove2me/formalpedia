-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_eq_A1_18
-- name    : SupplyFlex.SupplierLed.eq_A1_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:54.229036+00:00
-- url     : https://prove2.me/theorems/822f06fb-e91f-43d5-b824-611b9ffc7280
-- title:
--   (A1.18), proof of Theorem 6, Case 2, App. A1 p. 5 (PDF 37) — for log-concave f, s > r, c+(1−p)s ≤ r: p∫₀^{q°}xf ≥ ∫₀^{q̃}xf
-- statement:
--   In a standard model whose demand density $f$ is log-concave, suppose $s > r$ and $c + (1-p)s \le r$, and let $\tilde q$, $q^o$ be the solutions in $[0, \infty)$ of (1) and (2). Then
--   $$p\int_0^{q^o} x f(x)\,dx - \int_0^{\tilde q} x f(x)\,dx \ge 0,$$
--   i.e. $\mathcal H_2(s) \ge 0$ for the function $\mathcal H_2$ of (A1.18).
--
--   This is the buyer's half of Theorem 6 when $s > r$ and the price-only order is positive: under the flexibility contract the supplier guarantees nothing ($\bar\beta = 0$) and the buyer receives $q^o$ with probability $p$.
--
--   **Formalization Note.** $\int_0^q$ is the integral over $(0, q]$. Log-concavity is the published `ConvexOptimization.LogConcaveOn` on all of $\mathbb R$.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), App. A1 p. 5 (PDF 37), proof of Theorem 6, Case 2, (A1.18)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_LogConcaveOn
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- (A1.18), proof of Theorem 6, Case 2, App. A1 p. 5 (PDF 37): for log-concave demand,
`s > r` and `c + (1 − p)s ≤ r`, `p ∫₀^{q°} x f − ∫₀^{q̃} x f ≥ 0`. -/
theorem eq_A1_18 (M : Model) (hM : M.Std) (hlc : ConvexOptimization.LogConcaveOn Set.univ M.f)
    (qt qo : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hrs : M.r < M.s) (hcs : M.c + (1 - M.p) * M.s ≤ M.r) :
    ∫ x in Set.Ioc 0 qt, x * M.f x ≤ M.p * ∫ x in Set.Ioc 0 qo, x * M.f x := by sorry

end SupplyFlex.SupplierLed
