-- Prove2me | Theorems.Thm_PrivLearn_MaskedParity_orthogonality
-- name    : PrivLearn.MaskedParity.orthogonality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:51:19.800228+00:00
-- url     : https://prove2.me/theorems/1628a71a-6f6a-4a1a-8091-e17f73841ee1
-- title:
--   Proof of Theorem 5.16(2), p. 30 — ⟨c⁰_{r,a}, c⁰_{r′,a}⟩ = 1/2 if r = r′ and 0 otherwise
-- statement:
--   Let $d$ be a power of two and let examples be uniform on the MASKED-PARITY domain $D$. For $r,r'\in\{0,1\}^d$ and $a\in\{0,1\}$,
--   $$\langle c^0_{r,a},c^0_{r',a}\rangle=\begin{cases}1/2&\text{if } r=r',\\ 0&\text{if } r\neq r'.\end{cases}$$
--
--   So $\{\sqrt2\,c^0_{r,a}\}_{r\in\{0,1\}^d}$ is an orthonormal set for each $a$, the Fourier fact behind the lower bound.
--
--   **Formalization Note.** $c^0_{r,a}$ is the restriction of $c_{r,a}$ to the half $b=0$ (zero on $b=1$). $d\ge1$ follows from $d=2^m$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 30, proof of Theorem 5.16 part (2), display after the extension of c^0_{r,a}

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle

namespace PrivLearn.MaskedParity

/-- **Orthogonality display** (p. 30). Let `d` be a power of two. For `r, r′ ∈ {0,1}^d` and
`a ∈ {0,1}`, `⟨c^0_{r,a}, c^0_{r′,a}⟩ = 1/2` if `r = r′` and `0` if `r ≠ r′`. -/
theorem orthogonality {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) (r r' : Fin d → ZMod 2) (a : ZMod 2) :
    ip (half 0 (cMP r a)) (half 0 (cMP r' a)) = if r = r' then 1 / 2 else 0 := by sorry

end PrivLearn.MaskedParity
