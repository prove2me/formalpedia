-- Prove2me | Theorems.Thm_SDYM_chazy_mobius_invariance
-- name    : SDYM.chazy_mobius_invariance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T01:49:27.892048+00:00
-- url     : https://prove2.me/theorems/0478c5d4-029b-4aff-bd2e-22a1a67b90b1
-- title:
--   The Chazy equation admits the $\mathrm{SL}(2)$ symmetry (73)
-- statement:
--   Equation (73) of the source: the Chazy equation is invariant under the action
--
--   $$y(t) \;\longmapsto\; \tilde y(t) = (ct+d)^{-2}\,y\!\left(\frac{at+b}{ct+d}\right) - \frac{6c}{ct+d},\qquad ad-bc = 1,$$
--
--   of $\mathrm{SL}(2,\mathbb{C})$ on solutions. This is the weight-$2$ quasi-modular transformation law, and it is the reason the Chazy equation is tied to the theory of modular forms: the particular solution $y = i\pi E_2$ transforms exactly this way under $\mathrm{PSL}(2,\mathbb{Z})$.
--
--   The statement gives the transformed solution together with its first two derivatives, and asserts the Chazy equation on the set of $t$ for which $ct+d \neq 0$ and the Möbius image of $t$ lies in the original domain.
--
--   **Conventions shared with the rest of the mission.** All functions are complex-valued functions of a complex variable; a system is required to hold only at the points of an arbitrary set $s \subseteq \mathbb{C}$, with no openness, connectedness or holomorphy assumed; and each derivative that a statement mentions is carried by an explicit companion function tied to it by a pointwise differentiability assertion, so no statement ever refers to the value of a derivative that does not exist.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V.A p. 3168, Eq. (73)

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

namespace SDYM

theorem chazy_mobius_invariance
    (s : Set ℂ) (y y₁ y₂ : ℂ → ℂ) (h : IsChazySolution s y y₁ y₂)
    (a b c d : ℂ) (hdet : a * d - b * c = 1) :
    IsChazySolution {t : ℂ | c * t + d ≠ 0 ∧ (a * t + b) / (c * t + d) ∈ s}
      (fun t => y ((a * t + b) / (c * t + d)) / (c * t + d) ^ 2 - 6 * c / (c * t + d))
      (fun t => -2 * c * y ((a * t + b) / (c * t + d)) / (c * t + d) ^ 3
        + y₁ ((a * t + b) / (c * t + d)) / (c * t + d) ^ 4
        + 6 * c ^ 2 / (c * t + d) ^ 2)
      (fun t => 6 * c ^ 2 * y ((a * t + b) / (c * t + d)) / (c * t + d) ^ 4
        - 6 * c * y₁ ((a * t + b) / (c * t + d)) / (c * t + d) ^ 5
        + y₂ ((a * t + b) / (c * t + d)) / (c * t + d) ^ 6
        - 12 * c ^ 3 / (c * t + d) ^ 3) := by sorry

end SDYM
