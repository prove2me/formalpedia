-- Prove2me | Theorems.Thm_PrivLearn_MaskedParity_eq_7
-- name    : PrivLearn.MaskedParity.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:25.539979+00:00
-- url     : https://prove2.me/theorems/bafcfade-1fb7-4643-9a63-3f9a765c4afe
-- title:
--   Equation (7) — E[g(u, c_{r,a}(u))] = C_g + ⟨f⁰_g, c⁰_{r,a}⟩ + ⟨f¹_g, c¹_{r,a}⟩
-- statement:
--   Let examples be uniform on the MASKED-PARITY domain $D$. For every statistical query $g(u,y)$ with real values and every target $c_{r,a}$,
--   $$\mathbb E\bigl[g(x,i,b,c_{r,a}(x,i,b))\bigr]=C_g+\langle f^0_g,c^0_{r,a}\rangle+\langle f^1_g,c^1_{r,a}\rangle .$$
--
--   The true answer to a query splits into a part independent of the target, a part that depends only on $r$ (the half $b=1$), and the only part that depends on the mask bit $a$ (the half $b=0$).
--
--   **Formalization Note.** The identity holds for every real-valued $g$ because the labels are $\pm1$. The statement imposes no condition on $d$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 29, equation (7)

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle

namespace PrivLearn.MaskedParity

/-- **Equation (7)** (p. 29). For every real-valued query `g(u, y)` and every target `c_{r,a}`,
`E[g(u, c_{r,a}(u))] = C_g + ⟨f^0_g, c^0_{r,a}⟩ + ⟨f^1_g, c^1_{r,a}⟩`. -/
theorem eq_7 {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2) (g : Dom d → ℝ → ℝ) :
    qval (cMP r a) g =
      Cg g + ip (half 0 (fg g)) (half 0 (cMP r a)) + ip (half 1 (fg g)) (half 1 (cMP r a)) := by sorry

end PrivLearn.MaskedParity
