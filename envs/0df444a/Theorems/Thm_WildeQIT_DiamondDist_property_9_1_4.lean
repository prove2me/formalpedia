-- Prove2me | Theorems.Thm_WildeQIT_DiamondDist_property_9_1_4
-- name    : WildeQIT.DiamondDist.property_9_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:59.963971+00:00
-- url     : https://prove2.me/theorems/b25e31c9-ce02-43da-9095-dd8225471662
-- title:
--   Property 9.1.4 (Isometric Invariance): $\|UMV^\dagger\|_1=\|M\|_1$
-- statement:
--   Let $M\in\mathcal L(\mathcal H,\mathcal H')$ be an operator between finite-dimensional complex Hilbert spaces, and let $U:\mathcal H'\to\mathcal K'$ and $V:\mathcal H\to\mathcal K$ be isometries, that is $U^\dagger U=I_{\mathcal H'}$ and $V^\dagger V=I_{\mathcal H}$. Then the trace norm is invariant under multiplication by $U$ and $V$:
--
--   $$
--   \|UMV^\dagger\|_1=\|M\|_1 .
--   $$
--
--   Isometric invariance says that embedding a system into a larger one, on either side of an operator, does not change its trace norm; it gives, for instance, the invariance of the trace distance under isometric channels (Exercise 9.1.4).
--
--   Differences from the source:
--   - encoding: operators and isometries on finite-dimensional Hilbert spaces → complex matrices `M : Matrix m n ℂ`, `U : Matrix m' m ℂ`, `V : Matrix n' n ℂ` with `Uᴴ * U = 1`, `Vᴴ * V = 1`; reason: the book works in finite dimensions, and an isometry is a linear map with $U^\dagger U=I$
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 9.1.4, p. 252, eq. (9.14)

import Definitions.Def_WildeQIT_traceNorm

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 9.1.4, p. 252.
-/

open Matrix

namespace WildeQIT.DiamondDist

/-- **Property 9.1.4 (Isometric Invariance)** (Wilde, arXiv:1106.1445v8, p. 252, eq. (9.14)).
The trace norm is invariant under multiplication by isometries `U` and `V`:
`‖U M V†‖₁ = ‖M‖₁`.

Formalization Note: `M : Matrix m n ℂ` is an operator in `L(H, H′)`; `U : Matrix m' m ℂ` and
`V : Matrix n' n ℂ` are isometries (`U†U = I`, `V†V = I`), so `U M V† : Matrix m' n' ℂ`. -/
theorem property_9_1_4 {m n m' n' : Type} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq m] [DecidableEq n] [DecidableEq n']
    (M : Matrix m n ℂ) (U : Matrix m' m ℂ) (V : Matrix n' n ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    traceNorm (U * M * Vᴴ) = traceNorm M := by sorry

end WildeQIT.DiamondDist
