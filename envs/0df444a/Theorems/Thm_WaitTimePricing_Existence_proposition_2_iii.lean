-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_2_iii
-- name    : WaitTimePricing.Existence.proposition_2_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:58.228166+00:00
-- url     : https://prove2.me/theorems/b67532bb-94c3-47ec-97d1-1725a8954df1
-- title:
--   Proposition 2(iii) — $\Gamma(0)=U'(0)$ and $\Gamma$ is decreasing on $[0,\bar w]$
-- statement:
--   The joining price bound satisfies
--   $$\Gamma(0)=U'(0),$$
--   and $\Gamma(w)$ is decreasing (nonincreasing) in $w\in[0,\bar w]$.
--
--   The longer the wait, the lower the price the firm can charge and still attract a customer.
--
--   **Formalization Note** "Decreasing" is formalized as nonincreasing, the reading the paper's proof (p. 32) establishes and the paper's convention throughout.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 9, Proposition 2(iii)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 9, Proposition 2(iii).

`Γ(0) = U′(0)` and `Γ(w)` is decreasing in `w` (on `[0, w̄]`, where `Γ` is defined).

**Formalization Note.** "Decreasing" is formalized as nonincreasing (`AntitoneOn`), the reading
the paper's proof (p. 32) establishes ("`Γ(w₁) ≥ Γ(w₂)`, if `w₁ ≤ w₂`") and the paper's convention
for "decreasing" throughout. -/
theorem proposition_2_iii (M : Model) (hM : M.Standing) :
    Gamma M 0 = deriv M.U 0 ∧ AntitoneOn (Gamma M) (Icc 0 (wbar M)) := by sorry

end WaitTimePricing.Existence
