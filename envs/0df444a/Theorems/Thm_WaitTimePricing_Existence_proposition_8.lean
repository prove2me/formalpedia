-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_8
-- name    : WaitTimePricing.Existence.proposition_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:33.313983+00:00
-- url     : https://prove2.me/theorems/93e67f8a-e9f6-438e-afa9-3afe04392ecd
-- title:
--   Proposition 8 — $V^{\bar g}$ is differentiable on $[0,\bar w]$ and satisfies the DDE (12)
-- statement:
--   The function $V^{\bar g}$ is differentiable on $[0,\bar w]$, and for every $w\in[0,\bar w]$
--   $$\bar g=-{V^{\bar g}}'(w)+\lambda\max\Big\{\max_{p\in[0,\Gamma(w)]}\big[\mathbf v(p)-\alpha c(w)+V^{\bar g}(w+\mathtt t(p))-V^{\bar g}(w)\big],\ 0\Big\}.$$
--
--   This is the delay differential equation (12) for the constructed pair, the heart of the existence result.
--
--   **Formalization Note** For $w\in(0,\bar w]$ the statement asserts that $V^{\bar g}$ has a two-sided derivative at $w$ equal to the value the equation prescribes. Since $V^{\bar g}$ is constructed on $[0,\bar w+C]$, at $w=0$ the derivative is the right derivative.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 17, Proposition 8

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 17, Proposition 8.

`V^ḡ` is differentiable on `[0, w̄]`, and
`ḡ = −V^ḡ′(w) + λ max{max_{p∈[0,Γ(w)]} [v(p) − αc(w) + V^ḡ(w + t(p)) − V^ḡ(w)], 0}` for any
`w ∈ [0, w̄]`.

**Formalization Note.** The equation is stated as `HasDerivAt V^ḡ (λ max{…, 0} − ḡ) w` for
`w ∈ (0, w̄]` (two-sided derivative, never `deriv`). `V^ḡ` is constructed on `[0, w̄ + C]`, so at
`w = 0` the derivative is the right derivative (`HasDerivWithinAt` on `[0, ∞)`). -/
theorem proposition_8 (M : Model) (hM : M.Standing) (obj : Objective) :
    (∀ w ∈ Ioc 0 (wbar M),
      HasDerivAt (Vbar M obj) (M.lam * max (innerMax M obj (Vbar M obj) w) 0 - gbar M obj) w) ∧
    HasDerivWithinAt (Vbar M obj)
      (M.lam * max (innerMax M obj (Vbar M obj) 0) 0 - gbar M obj) (Ici 0) 0 := by sorry

end WaitTimePricing.Existence
