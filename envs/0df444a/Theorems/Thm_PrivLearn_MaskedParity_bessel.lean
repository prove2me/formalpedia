-- Prove2me | Theorems.Thm_PrivLearn_MaskedParity_bessel
-- name    : PrivLearn.MaskedParity.bessel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:38.495903+00:00
-- url     : https://prove2.me/theorems/16f32ed1-6ce4-448d-a23c-4796510cc8c6
-- title:
--   Proof of Theorem 5.16(2), p. 30 — Σ_{(r,a)} 2⟨f⁰_g, c⁰_{r,a}⟩² ≤ 1
-- statement:
--   Let $d$ be a power of two, let examples be uniform on the MASKED-PARITY domain $D$, and let $g$ be a statistical query with values in $\{+1,-1\}$ on labels $y\in\{+1,-1\}$. Then
--   $$\sum_{(r,a)\in\{0,1\}^d\times\{0,1\}}2\cdot\langle f^0_g,c^0_{r,a}\rangle^2\le1 .$$
--
--   This Bessel inequality bounds the total correlation of one query with all the $b=0$ halves of the concepts, which is what limits how many targets a single nonadaptive query can distinguish.
--
--   **Formalization Note.** The range condition on $g$ is the paper's ($g:\{0,1\}^d\times\{0,1\}^{\log d}\times\{0,1\}\times\{+1,-1\}\to\{+1,-1\}$, p. 29); values of $g$ at other labels play no role.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 30, proof of Theorem 5.16 part (2), display 'Summing the two previous equations'

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle

namespace PrivLearn.MaskedParity

/-- **Bessel display** (p. 30). Let `d` be a power of two and let `g` be a statistical query
with values `±1` on labels `±1`. Then
`∑_{(r,a) ∈ {0,1}^d × {0,1}} 2 · ⟨f^0_g, c^0_{r,a}⟩² ≤ 1`. -/
theorem bessel {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) (g : Dom d → ℝ → ℝ)
    (hg : ∀ u y, (y = 1 ∨ y = -1) → (g u y = 1 ∨ g u y = -1)) :
    ∑ ra : (Fin d → ZMod 2) × ZMod 2, 2 * ip (half 0 (fg g)) (half 0 (cMP ra.1 ra.2)) ^ 2 ≤ 1 := by sorry

end PrivLearn.MaskedParity
