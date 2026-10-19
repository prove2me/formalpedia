-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_7
-- name    : WaitTimePricing.Existence.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:37.809742+00:00
-- url     : https://prove2.me/theorems/18b0c53e-bb5a-48fd-b8bf-a8d2a2aad1e0
-- title:
--   Proposition 7 — boundary condition (13) for $(\bar g,V^{\bar g})$
-- statement:
--   The pair $(\bar g,V^{\bar g})$ satisfies the boundary condition (13):
--   $$\bar g=\lambda\max\Big\{\max_{p\in[0,\Gamma(0)]}\big[\mathbf v(p)+V^{\bar g}(\mathtt t(p))-V^{\bar g}(0)\big],\ 0\Big\}.$$
--
--   **Formalization Note** The inner maximum is the shared one of the optimality equations at $w=0$, whose extra term $\alpha c(0)$ vanishes because $c(0)=0$.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 17, Proposition 7

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 17, Proposition 7.

`ḡ = λ max{max_{p∈[0,Γ(0)]} [v(p) + V^ḡ(t(p)) − V^ḡ(0)], 0}`, i.e. `ḡ`, `V^ḡ` satisfy (13).

**Formalization Note.** The inner max is `innerMax` at `w = 0`, whose extra term `α c(0)` is zero
since `c(0) = 0`. -/
theorem proposition_7 (M : Model) (hM : M.Standing) (obj : Objective) :
    gbar M obj = M.lam * max (innerMax M obj (Vbar M obj) 0) 0 := by sorry

end WaitTimePricing.Existence
