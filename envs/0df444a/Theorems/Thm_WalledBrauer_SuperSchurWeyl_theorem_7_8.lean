-- Prove2me | Theorems.Thm_WalledBrauer_SuperSchurWeyl_theorem_7_8
-- name    : WalledBrauer.SuperSchurWeyl.theorem_7_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:15.247358+00:00
-- url     : https://prove2.me/theorems/2ebf8f8b-f490-4003-8f7e-60b1a98b68fa
-- title:
--   Theorem 7.8 — mixed Schur–Weyl duality: Ψ : B_{r,s}(m−n) ↠ End_g(V^{⊗r} ⊗ W^{⊗s}), injective iff r+s < (m+1)(n+1)
-- statement:
--   Let $m, n, r, s \ge 0$, $\delta = m - n$, and $\mathfrak g = \mathfrak{gl}_{m|n}(\mathbb C)$ with natural supermodule $V$ and its dual $W = V^*$. Let
--
--   $$
--   \Psi^{m,n}_{r,s} : B_{r,s}(\delta) \to \operatorname{End}_{\mathfrak g}(V^{\otimes r} \otimes W^{\otimes s})^{\mathrm{op}}
--   $$
--
--   be the homomorphism (7.12) given by the right action (7.7) of the walled Brauer algebra on mixed tensor space. Then:
--
--   1. $\Psi^{m,n}_{r,s}$ is surjective: its image is exactly the space $\operatorname{End}_{\mathfrak g}(V^{\otimes r} \otimes W^{\otimes s})$ of all (not necessarily homogeneous) $\mathfrak g$-supermodule endomorphisms;
--   2. $\Psi^{m,n}_{r,s}$ is injective if and only if
--   $$
--   r + s < (m+1)(n+1).
--   $$
--
--   This is mixed Schur–Weyl duality for $\mathfrak{gl}_{m|n}(\mathbb C)$. It holds for all $m, n, r, s$, including $m = 0$ or $n = 0$ (the purely even and purely odd cases) and $r = 0$ or $s = 0$. In the paper it is the first step of the proof of the main theorem (Theorem 1.1 = Theorem 8.10), identifying $B_{r,s}(\delta)$ modulo $\ker \Psi^{m,n}_{r,s}$ with an endomorphism algebra.
--
--   **Formalization Note** $B_{r,s}(\delta)$ enters as the vector space with basis the walled Brauer diagrams (`WalledDiagram r s →₀ ℂ`), and `Psi m n r s` is the linear extension of (7.7); surjectivity and injectivity of the algebra homomorphism (7.12) are properties of this linear map, and the $^{\mathrm{op}}$ changes only the multiplication. The range clause is an equality: it contains both the inclusion of the image in $\operatorname{End}_{\mathfrak g}$ and the surjectivity. `EndG m n (mixed r s)` is the super-commutant of the whole of $\mathfrak g$, odd part and signs included.
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, p. 56, Theorem 7.8 and (7.12) (p. 53); standing assumptions p. 48

import Mathlib
import Definitions.Def_WalledBrauer_SuperSchurWeyl_Weights

namespace WalledBrauer.SuperSchurWeyl

/-- Theorem 7.8 (p. 56), mixed Schur–Weyl duality for `gl_{m|n}(ℂ)`:
`Ψ^{m,n}_{r,s} : B_{r,s}(m - n) → End_g(V^{⊗ r} ⊗ W^{⊗ s})` is surjective (its range is exactly
`End_g`), and it is injective iff `r + s < (m + 1)(n + 1)`. -/
theorem theorem_7_8 (m n r s : ℕ) :
    LinearMap.range (Psi m n r s) = EndG m n (mixed r s) ∧
    (Function.Injective (Psi m n r s) ↔ r + s < (m + 1) * (n + 1)) := by sorry

end WalledBrauer.SuperSchurWeyl
