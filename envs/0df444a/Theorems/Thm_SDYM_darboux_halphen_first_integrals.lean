-- Prove2me | Theorems.Thm_SDYM_darboux_halphen_first_integrals
-- name    : SDYM.darboux_halphen_first_integrals
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T01:29:05.885552+00:00
-- url     : https://prove2.me/theorems/23548164-a453-4086-a0d5-a37a8b91cbc5
-- title:
--   The three constants $\alpha^2,\beta^2,\gamma^2$ of the generalized Darboux–Halphen system
-- statement:
--   Equation (55) of the source. For a solution of the generalized Darboux–Halphen system (52)–(53) with pairwise distinct $\omega_j$, the three quantities
--
--   $$\alpha^2 = \frac{\tau_1^2}{(\omega_1-\omega_2)(\omega_3-\omega_1)},\qquad \beta^2 = \frac{\tau_2^2}{(\omega_2-\omega_3)(\omega_1-\omega_2)},\qquad \gamma^2 = \frac{\tau_3^2}{(\omega_3-\omega_1)(\omega_2-\omega_3)}$$
--
--   are constants of the motion. They are what reduces the six-dimensional system (52)–(53) to the third-order system (52) with $\tau^2$ given by the closed expression (56), and they are the parameters of the associated Schwarzian triangle function.
--
--   Constancy is stated in the pointwise form appropriate to an arbitrary domain: each of the three quantities, as a function of $t$, has derivative zero at every point of the domain. On a connected open domain this is equivalent to being constant.
--
--   **Conventions shared with the rest of the mission.** All functions are complex-valued functions of a complex variable; a system is required to hold only at the points of an arbitrary set $s \subseteq \mathbb{C}$, with no openness, connectedness or holomorphy assumed; and each derivative that a statement mentions is carried by an explicit companion function tied to it by a pointwise differentiability assertion, so no statement ever refers to the value of a derivative that does not exist.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V p. 3165, Eq. (55) together with the sentence "these equations show that α², β², γ² are constants"

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

namespace SDYM

theorem darboux_halphen_first_integrals
    (s : Set ℂ) (w₁ w₂ w₃ x₁ x₂ x₃ : ℂ → ℂ)
    (h : IsGeneralizedDHSolution s w₁ w₂ w₃ x₁ x₂ x₃)
    (hdist : ∀ t ∈ s, w₁ t ≠ w₂ t ∧ w₂ t ≠ w₃ t ∧ w₃ t ≠ w₁ t) :
    (∀ t ∈ s, HasDerivAt
        (fun z => x₁ z ^ 2 / ((w₁ z - w₂ z) * (w₃ z - w₁ z))) 0 t) ∧
    (∀ t ∈ s, HasDerivAt
        (fun z => x₂ z ^ 2 / ((w₂ z - w₃ z) * (w₁ z - w₂ z))) 0 t) ∧
    (∀ t ∈ s, HasDerivAt
        (fun z => x₃ z ^ 2 / ((w₃ z - w₁ z) * (w₂ z - w₃ z))) 0 t) := by sorry

end SDYM
