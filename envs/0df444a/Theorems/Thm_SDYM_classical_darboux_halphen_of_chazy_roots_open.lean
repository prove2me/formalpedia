-- Prove2me | Theorems.Thm_SDYM_classical_darboux_halphen_of_chazy_roots_open
-- name    : SDYM.classical_darboux_halphen_of_chazy_roots_open
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-24T13:44:26.338899+00:00
-- url     : https://prove2.me/theorems/11ac2538-3d7f-4a5d-b9b0-0fabcca7aa23
-- title:
--   Darboux–Halphen from Chazy: the roots of $\omega^3+\tfrac12 y\omega^2+\tfrac12 y'\omega+\tfrac1{12}y''$
-- statement:
--   The converse direction of the Darboux–Halphen–Chazy correspondence. Given a solution $y$ of the Chazy equation, let $\omega_1, \omega_2, \omega_3$ be the three roots of the cubic
--
--   $$\omega^3 + \frac{1}{2}y\,\omega^2 + \frac{1}{2}\frac{dy}{dt}\,\omega + \frac{1}{12}\frac{d^2y}{dt^2} = 0 .$$
--
--   If the $\omega_j$ are distinct (and depend differentiably on $t$), they solve the classical Darboux–Halphen system. Distinctness is essential and not a technical convenience: the three Darboux–Halphen equations are recovered from the derivatives of the three coefficients of the cubic by inverting a Vandermonde matrix in $\omega_1, \omega_2, \omega_3$, which is singular as soon as two roots coincide.
--
--   The hypothesis that the $\omega_j$ are the roots is stated as the factorization of the cubic: for each $t$ in the domain and every $z$,
--
--   $$z^3 + \frac{y(t)}{2}z^2 + \frac{y_1(t)}{2}z + \frac{y_2(t)}{12} = (z-\omega_1(t))(z-\omega_2(t))(z-\omega_3(t)).$$
--
--   **Conventions shared with the rest of the mission.** All functions are complex-valued functions of a complex variable; a system is required to hold at the points of an open set $s \subseteq \mathbb{C}$ (openness is assumed in this corrected statement; no connectedness or holomorphy is assumed); and each derivative that a statement mentions is carried by an explicit companion function tied to it by a pointwise differentiability assertion, so no statement ever refers to the value of a derivative that does not exist.
--
--   **Correction (moderator).** The set $s$ is now required to be open. Without openness the root identities hold only at isolated points and say nothing about the derivatives of $\omega_j$ there, which refutes the statement; on an open set they can be differentiated and the source's argument goes through.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V.A p. 3168, the sentence "given a solution y of the Chazy equation (71), let ω1, ω2, ω3 be the three roots of the cubic equation ... If the ωj's are distinct, then they solve the classical Darboux–Halphen system" (the displayed cubic; the source's "1/2 dy/dz" is a typographical slip for "1/2 dy/dt")

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

namespace SDYM

theorem classical_darboux_halphen_of_chazy_roots_open
    (s : Set ℂ) (hs : IsOpen s) (y y₁ y₂ w₁ w₂ w₃ : ℂ → ℂ)
    (hy : IsChazySolution s y y₁ y₂)
    (hw₁ : ∀ t ∈ s, DifferentiableAt ℂ w₁ t)
    (hw₂ : ∀ t ∈ s, DifferentiableAt ℂ w₂ t)
    (hw₃ : ∀ t ∈ s, DifferentiableAt ℂ w₃ t)
    (hroots : ∀ t ∈ s, ∀ z : ℂ,
      z ^ 3 + y t / 2 * z ^ 2 + y₁ t / 2 * z + y₂ t / 12
        = (z - w₁ t) * (z - w₂ t) * (z - w₃ t))
    (hdist : ∀ t ∈ s, w₁ t ≠ w₂ t ∧ w₂ t ≠ w₃ t ∧ w₃ t ≠ w₁ t) :
    IsClassicalDHSolution s w₁ w₂ w₃ := by sorry

end SDYM
