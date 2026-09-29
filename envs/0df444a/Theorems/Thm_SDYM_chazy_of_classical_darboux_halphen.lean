-- Prove2me | Theorems.Thm_SDYM_chazy_of_classical_darboux_halphen
-- name    : SDYM.chazy_of_classical_darboux_halphen
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T01:30:38.488239+00:00
-- url     : https://prove2.me/theorems/03b78a94-44e8-4330-b56b-fdf9c15c8794
-- title:
--   Chazy from Darboux–Halphen: $y = -2(\omega_1+\omega_2+\omega_3)$
-- statement:
--   Let $\omega_1,\omega_2,\omega_3$ solve the classical Darboux–Halphen system
--
--   $$\dot\omega_1 = \omega_2\omega_3 - \omega_1(\omega_2+\omega_3)$$
--
--   together with its two cyclic images. Then $y := -2(\omega_1+\omega_2+\omega_3)$ solves the classical Chazy equation. The computation goes through the elementary symmetric functions $e_1, e_2, e_3$ of the $\omega_i$, which satisfy $\dot e_1 = -e_2$, $\dot e_2 = -6e_3$ and $\dot e_3 = e_2^2 - 4e_1e_3$, so that the first two derivatives of $y$ are $2e_2$ and $-12e_3$; the statement records them in that form.
--
--   **Conventions shared with the rest of the mission.** All functions are complex-valued functions of a complex variable; a system is required to hold only at the points of an arbitrary set $s \subseteq \mathbb{C}$, with no openness, connectedness or holomorphy assumed; and each derivative that a statement mentions is carried by an explicit companion function tied to it by a pointwise differentiability assertion, so no statement ever refers to the value of a derivative that does not exist.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V.A p. 3168, the sentence "Let ω1, ω2, ω3 be a solution of (52) with τ = 0 and define y := -2(ω1+ω2+ω3). Then y is a solution of the equation (71)"

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

namespace SDYM

theorem chazy_of_classical_darboux_halphen
    (s : Set ℂ) (w₁ w₂ w₃ : ℂ → ℂ) (h : IsClassicalDHSolution s w₁ w₂ w₃) :
    IsChazySolution s
      (fun t => -2 * (w₁ t + w₂ t + w₃ t))
      (fun t => 2 * (w₁ t * w₂ t + w₂ t * w₃ t + w₃ t * w₁ t))
      (fun t => -12 * (w₁ t * w₂ t * w₃ t)) := by sorry

end SDYM
