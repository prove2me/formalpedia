-- Prove2me | Theorems.Thm_WildeQIT_DiamondDist_property_9_1_6
-- name    : WildeQIT.DiamondDist.property_9_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:59.016975+00:00
-- url     : https://prove2.me/theorems/f3ef7ded-0d9a-4f52-abe9-f0b1ced9fa5a
-- title:
--   Property 9.1.6 (Variational characterization): $\|M\|_1=\max_U|\operatorname{Tr}\{MU\}|$
-- statement:
--   Let $M\in\mathcal L(\mathcal H)$ be a square operator on a finite-dimensional complex Hilbert space. Then
--
--   $$
--   \|M\|_1=\max_{U}\,\bigl|\operatorname{Tr}\{MU\}\bigr| ,
--   $$
--
--   where the maximum is over all unitary operators $U$ on $\mathcal H$. In particular the maximum is attained: some unitary $U$ achieves $|\operatorname{Tr}\{MU\}|=\|M\|_1$, and $|\operatorname{Tr}\{MU\}|\le\|M\|_1$ for every unitary $U$.
--
--   This characterization is the tool for proving the triangle inequality of the trace norm for square operators (Exercise 9.1.1).
--
--   Differences from the source:
--   - encoding: $\max_U$ → `IsGreatest` of the set $\{|\operatorname{Tr}\{MU\}| : U \text{ unitary}\}$; reason: states that the maximum exists and equals $\|M\|_1$
--   - encoding: square operator on a finite-dimensional Hilbert space → `M : Matrix n n ℂ`, unitaries `Matrix.unitaryGroup n ℂ`; reason: the book works in finite dimensions
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 9.1.6, p. 252, eq. (9.16)

import Definitions.Def_WildeQIT_traceNorm
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 9.1.6, p. 252.
-/

open Matrix

namespace WildeQIT.DiamondDist

/-- **Property 9.1.6 (Variational characterization)** (Wilde, arXiv:1106.1445v8, p. 252,
eq. (9.16)). For a square operator `M ∈ L(H)`, `‖M‖₁ = max_U |Tr{MU}|`, where the optimization
is with respect to all unitary operators.

Formalization Note: the maximum is stated as `IsGreatest`: `‖M‖₁` is attained by some unitary
and bounds `|Tr{MU}|` for every unitary `U ∈ Matrix.unitaryGroup n ℂ`. -/
theorem property_9_1_6 {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    IsGreatest {x : ℝ | ∃ U ∈ Matrix.unitaryGroup n ℂ, x = ‖(M * U).trace‖} (traceNorm M) := by sorry

end WildeQIT.DiamondDist
