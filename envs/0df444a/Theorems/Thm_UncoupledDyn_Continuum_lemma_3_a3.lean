-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_lemma_3_a3
-- name    : UncoupledDyn.Continuum.lemma_3_a3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:38.140289+00:00
-- url     : https://prove2.me/theorems/e4a56d49-b74b-4f1e-b32a-eddff57e5f5d
-- title:
--   Proof of LEMMA 3, p. 1832 — the coefficient a₃ of λ in det(J − λI) is 3 det(J¹)tr(J²) + 3 det(J²)tr(J¹)
-- statement:
--   Let $J^1,J^2$ be real $2\times2$ matrices and let
--   $$J=\begin{bmatrix}J^1&-2J^1\\-2J^2&J^2\end{bmatrix}.$$
--   The coefficient $a_3$ of $\lambda$ in the characteristic polynomial $\det(J-\lambda I)$ of $J$ is
--   $$a_3=3\det(J^1)\,\operatorname{trace}(J^2)+3\det(J^2)\,\operatorname{trace}(J^1).$$
--
--   Combined with the sign information on $\det J^i$ and $\operatorname{trace}J^i$, this coefficient is what forces an eigenvalue of $J$ into the right half-plane.
--
--   **Formalization Note.** Mathlib's characteristic polynomial is $\det(\lambda I-J)$; for a $4\times4$ matrix it equals $\det(J-\lambda I)$, so $a_3$ is its coefficient of $\lambda^1$. The identity was checked symbolically (sympy) when the mission was planned.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1832, PROOF of LEMMA 3, display of a₃

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- Proof of LEMMA 3, p. 1832: the coefficient `a₃` of `λ` in the characteristic polynomial of
`J = [J¹, −2J¹; −2J², J²]` is `3 det(J¹) trace(J²) + 3 det(J²) trace(J¹)`. -/
theorem lemma_3_a3 (J1 J2 : Matrix (Fin 2) (Fin 2) ℝ) :
    (blockJ J1 J2).charpoly.coeff 1 = 3 * J1.det * J2.trace + 3 * J2.det * J1.trace := by sorry

end UncoupledDyn.Continuum
