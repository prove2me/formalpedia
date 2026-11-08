-- Prove2me | Theorems.Thm_ParityCubes_complement_input
-- name    : ParityCubes.complement_input
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:15:54.78841+00:00
-- url     : https://prove2.me/theorems/d30c3092-a247-4fb3-82de-58f00ef06ea9
-- title:
--   §2.1 — complementing an input variable changes no derivative
-- statement:
--   Let $g$ be $f$ with the input $x_i$ complemented. For every set $S$ and every $y$, $D_Sg(y)=D_Sf(y')$, where $y'$ is $y$ with $y_i$ complemented. Hence $f$ and $g$ have the same certificates and the same zero cubes, and $\mathrm{cert}(g)=\mathrm{cert}(f)$, $\zeta(g)=\zeta(f)$.
--
--   The proof of Theorem 4.1 uses this to pass from $Q$ to the positive formula $Q^+$.
--
--   Differences from the source: none.
-- source:
--   Sheshadri, Smirnov, The Complexity of Choosing Parity Projections, arXiv:2611.00289 (manuscript sha256 95994d2d…), §2.1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_ParityCubes_cubeSum

set_option autoImplicit false

namespace ParityCubes

/-- **Complementing an input variable changes no derivative** (Sheshadri–Smirnov, arXiv:2611.00289,
manuscript sha256 95994d2d…, §2.1, p.4 (PDF p.5)). Let `g` be `f` with `x_i` complemented. Then
`D_S g (y) = D_S f (y′)`, where `y′` is `y` with `y_i` complemented, for every `S`; so `f` and `g`
have the same certificates and the same zero cubes, and `cert(g) = cert(f)`, `ζ(g) = ζ(f)`. -/
theorem complement_input {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool) (i : α) :
    let flip : (α → Bool) → (α → Bool) := fun x => Function.update x i (!x i)
    let g : (α → Bool) → Bool := fun x => f (flip x)
    (∀ (S : Finset α) (y : α → Bool), cubeSum g S y = cubeSum f S (flip y)) ∧
    (∀ S : Finset α, IsCertificate g S ↔ IsCertificate f S) ∧
    (∀ S : Finset α, IsZeroCube g S ↔ IsZeroCube f S) ∧
    cert g = cert f ∧ zeta g = zeta f := by sorry

end ParityCubes
