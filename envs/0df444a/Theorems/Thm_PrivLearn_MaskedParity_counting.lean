-- Prove2me | Theorems.Thm_PrivLearn_MaskedParity_counting
-- name    : PrivLearn.MaskedParity.counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:35.038394+00:00
-- url     : https://prove2.me/theorems/867577dc-496a-4cf0-9939-6cff56837424
-- title:
--   Proof of Theorem 5.16(2), p. 30 — at most 2^{2d/3−1} concepts have |⟨f⁰_g, c⁰_{r,a}⟩| ≥ 1/2^{d/3}
-- statement:
--   Let $d$ be a power of two, let examples be uniform on the MASKED-PARITY domain $D$, and let $g$ be a statistical query with values in $\{+1,-1\}$ on labels $y\in\{+1,-1\}$. Then
--   $$\#\Bigl\{(r,a)\in\{0,1\}^d\times\{0,1\}:\ |\langle f^0_g,c^0_{r,a}\rangle|\ge\frac1{2^{d/3}}\Bigr\}\le2^{2d/3-1}.$$
--
--   A single query is correlated, above the threshold $2^{-d/3}$, with only an exponentially small fraction $2^{-d/3-2}$ of the $2^{d+1}$ concepts.
--
--   **Formalization Note.** $2^{d/3}$ and $2^{2d/3-1}$ are real powers of $2$ (`Real.rpow`); $d/3$ is real division. The concepts are counted as pairs $(r,a)$; distinct pairs give distinct concepts.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 30, proof of Theorem 5.16 part (2), sentence after the display Σ 2⟨f⁰_g, c⁰_{r,a}⟩² ≤ 1

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle

namespace PrivLearn.MaskedParity

/-- **Counting display** (p. 30). Let `d` be a power of two and let `g` be a statistical query
with values `±1` on labels `±1`. At most `2^{2d/3 − 1}` pairs `(r, a)` have
`|⟨f^0_g, c^0_{r,a}⟩| ≥ 1/2^{d/3}` (real exponents). -/
theorem counting {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) (g : Dom d → ℝ → ℝ)
    (hg : ∀ u y, (y = 1 ∨ y = -1) → (g u y = 1 ∨ g u y = -1)) :
    ((Finset.univ.filter fun ra : (Fin d → ZMod 2) × ZMod 2 =>
        1 / (2 : ℝ) ^ ((d : ℝ) / 3) ≤ |ip (half 0 (fg g)) (half 0 (cMP ra.1 ra.2))|).card : ℝ) ≤
      (2 : ℝ) ^ (2 * (d : ℝ) / 3 - 1) := by sorry

end PrivLearn.MaskedParity
