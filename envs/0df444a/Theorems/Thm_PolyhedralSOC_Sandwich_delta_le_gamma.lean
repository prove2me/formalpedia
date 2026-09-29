-- Prove2me | Theorems.Thm_PolyhedralSOC_Sandwich_delta_le_gamma
-- name    : PolyhedralSOC.Sandwich.delta_le_gamma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:53:58.471156+00:00
-- url     : https://prove2.me/theorems/aa65a284-0e1a-4e7c-85be-373e67900e36
-- title:
--   Proof of Proposition 4.1 — t ≤ R/(1−γ(ε)), whence δ ≤ γ(ε)
-- statement:
--   Let $r>0$, $\varepsilon>0$, $t\ge0$ and $R$ be real numbers with $\gamma(\varepsilon)=R\varepsilon/r<1$, and let
--   $$
--   \delta=\frac{\varepsilon t}{r+\varepsilon t}.
--   $$
--   If $(1-\delta)t\le R$, then
--   $$
--   t\le\frac{R}{1-\gamma(\varepsilon)}\qquad\text{and}\qquad \delta\le\gamma(\varepsilon).
--   $$
--
--   This is the arithmetic step that closes the proof of Proposition 4.1: it bounds the interpolation parameter $\delta$ of the feasible point $x_\delta$ by $\gamma(\varepsilon)=R\varepsilon/r$.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 203 (PDF 11), proof of Proposition 4.1

import Mathlib

namespace PolyhedralSOC.Sandwich

/-- Proof of Proposition 4.1, p. 203 (PDF p. 11) (Ben-Tal & Nemirovski, *On Polyhedral
Approximations of the Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001)):
if `r > 0`, `ε > 0`, `t ≥ 0`, `γ(ε) = Rε/r < 1`, `δ = εt/(r + εt)` and `(1 − δ)t ≤ R`,
then `t ≤ R/(1 − γ(ε))`, whence `δ ≤ γ(ε)`. -/
theorem delta_le_gamma (r ε R t δ : ℝ) (hr : 0 < r) (hε : 0 < ε) (ht : 0 ≤ t)
    (hγ : R * ε / r < 1) (hδ : δ = ε * t / (r + ε * t)) (hbound : (1 - δ) * t ≤ R) :
    t ≤ R / (1 - R * ε / r) ∧ δ ≤ R * ε / r := by sorry

end PolyhedralSOC.Sandwich
