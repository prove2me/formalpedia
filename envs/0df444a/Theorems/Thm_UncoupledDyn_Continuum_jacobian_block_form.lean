-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_jacobian_block_form
-- name    : UncoupledDyn.Continuum.jacobian_block_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:20.966636+00:00
-- url     : https://prove2.me/theorems/537760d3-eafb-4be0-a2df-99979fc5271e
-- title:
--   §II, p. 1832 — from fⁱ(2xʲ, xʲ) = 0 near 0: 2∂fⁱ/∂xⁱ + ∂fⁱ/∂xʲ = 0, so J = [J¹, −2J¹; −2J², J²]
-- statement:
--   Let $f=(f^1,f^2):D\times D\to\mathbb R^2\times\mathbb R^2$ be $C^1$, and suppose that for each player $i$ (with $j=3-i$)
--   $$f^i(2x^j,x^j)=0\qquad\text{for all }x^j\text{ in a neighborhood of }0,$$
--   where $2x^j$ is player $i$'s strategy and $x^j$ is player $j$'s. Then for all $k,l=1,2$,
--   $$2\,\frac{\partial f^i_k(0,0)}{\partial x^i_l}+\frac{\partial f^i_k(0,0)}{\partial x^j_l}=0,$$
--   so that, with $J^i=(\partial f^i_k(0,0)/\partial x^i_l)_{k,l}$, the $4\times4$ Jacobian matrix of $(f^1,f^2)$ at $\bar x=(0,0)$ is
--   $$J=\begin{bmatrix}J^1&-2J^1\\-2J^2&J^2\end{bmatrix}.$$
--
--   In the paper $f^i=F^i(\cdot\,;u_0^i)$, and the vanishing hypothesis comes from Lemma 2; this step reduces the stability question at $\Gamma_0$ to a matrix problem.
--
--   **Formalization Note.** Rows and columns of the Jacobian are indexed by (player, coordinate), with coordinates the real and imaginary parts; derivatives are taken within $X$, which at the interior point $(0,0)$ is the ordinary derivative. The block matrix is the mission's `blockJ`, written in the same indexing.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1832, §II, display after "Differentiating and then evaluating at x̄ = (0, 0) gives" and the display of J

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- §II, p. 1832: if `f = (f¹, f²)` is `C¹` on `X` and `fⁱ(2xʲ, xʲ) = 0` for all `xʲ` in a
neighborhood of `0` (with `2xʲ` in player `i`'s slot), then `2∂fⁱ_k(0,0)/∂xⁱ_l + ∂fⁱ_k(0,0)/∂xʲ_l = 0`,
so the `4 × 4` Jacobian of `f` at `(0, 0)` is `J = [J¹, −2J¹; −2J², J²]` with
`Jⁱ = (∂fⁱ_k(0,0)/∂xⁱ_l)_{k,l}`. -/
theorem jacobian_block_form (f : (Fin 2 → ℂ) → (Fin 2 → ℂ)) (hf : ContDiffOn ℝ 1 f X)
    (hvan : ∀ i : Fin 2, ∀ᶠ w in nhds (0 : ℂ), f (fun m => if m = i then 2 * w else w) i = 0) :
    jacOf f 0 = blockJ (ownJacOf f 0 0) (ownJacOf f 1 0) := by sorry

end UncoupledDyn.Continuum
