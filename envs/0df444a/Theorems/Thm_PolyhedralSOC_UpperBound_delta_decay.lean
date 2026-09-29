-- Prove2me | Theorems.Thm_PolyhedralSOC_UpperBound_delta_decay
-- name    : PolyhedralSOC.UpperBound.delta_decay
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:49:08.125377+00:00
-- url     : https://prove2.me/theorems/5ac27f0f-85e2-4b22-8b47-333c05c00cd3
-- title:
--   Proposition 2.1, Eq. (9) — $\delta(\nu)=O(1/4^\nu)$
-- statement:
--   The accuracy $\delta(\nu)=1/\cos(\pi/2^{\nu+1})-1$ of system (8) decays geometrically: there is an absolute constant $C>0$ such that for every positive integer $\nu$
--   $$\delta(\nu)\le\frac{C}{4^\nu}.$$
--
--   This is what makes the size of the approximation logarithmic in the accuracy: $\nu=O(\ln(1/\varepsilon))$ steps suffice for accuracy $\varepsilon$.
--
--   **Formalization Note** The paper writes $\delta(\nu)=O(1/4^\nu)$; this states exactly that, with an existential constant chosen before $\nu$.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 199, Proposition 2.1, Eq. (9)

import Mathlib
import Definitions.Def_PolyhedralSOC_UpperBound_System8

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 2.1, Eq. (9), p. 199 (PDF p. 7):
`δ(ν) = 1/cos(π/2^{ν+1}) − 1 = O(1/4^ν)`, i.e. there is an absolute constant `C > 0`
with `δ(ν) ≤ C / 4^ν` for every positive integer `ν`. -/
theorem delta_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℕ, 1 ≤ ν → delta ν ≤ C / 4 ^ ν := by sorry

end PolyhedralSOC.UpperBound
