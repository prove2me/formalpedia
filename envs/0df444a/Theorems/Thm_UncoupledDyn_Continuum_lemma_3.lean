-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_lemma_3
-- name    : UncoupledDyn.Continuum.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:36.942243+00:00
-- url     : https://prove2.me/theorems/47cbf4ff-8c6e-4264-8752-7cbe5c80f994
-- title:
--   LEMMA 3, p. 1832 — if J¹ and J² are stable then J = [J¹, −2J¹; −2J², J²] has an eigenvalue with positive real part
-- statement:
--   Let $J^1,J^2$ be real $2\times2$ matrices all of whose eigenvalues have negative real parts. Then the $4\times4$ matrix
--   $$J=\begin{bmatrix}J^1&-2J^1\\-2J^2&J^2\end{bmatrix}$$
--   has at least one eigenvalue $\lambda\in\mathbb C$ with $\operatorname{Re}\lambda>0$.
--
--   Together with Lemma 2 and the block form of the Jacobian at $\Gamma_0$, this shows that the Nash equilibrium of $\Gamma_0$ cannot be a stable rest point of an uncoupled dynamic.
--
--   **Formalization Note.** Eigenvalues are the elements of the spectrum of the matrix viewed over $\mathbb C$; the hypotheses use the published predicate `FatkhullinPolyak.Discrete.IsHurwitz`.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1832, LEMMA 3

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- LEMMA 3, p. 1832: if the eigenvalues of `J¹` and `J²` have negative real parts, then
`J = [J¹, −2J¹; −2J², J²]` has at least one eigenvalue with positive real part. -/
theorem lemma_3 (J1 J2 : Matrix (Fin 2) (Fin 2) ℝ) (h1 : FatkhullinPolyak.Discrete.IsHurwitz J1)
    (h2 : FatkhullinPolyak.Discrete.IsHurwitz J2) :
    ∃ z ∈ spectrum ℂ ((blockJ J1 J2).map (algebraMap ℝ ℂ)), 0 < z.re := by sorry

end UncoupledDyn.Continuum
