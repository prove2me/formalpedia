-- Prove2me | Theorems.Thm_SDYM_matrix_flow_of_generalized_darboux_halphen
-- name    : SDYM.matrix_flow_of_generalized_darboux_halphen
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T01:27:41.542303+00:00
-- url     : https://prove2.me/theorems/b39f2927-09a2-4ffe-921a-f328544f1d9b
-- title:
--   The factorization $M = P(d+a)P^{T}$ solves the matrix flow (51)
-- statement:
--   The reduction of the matrix flow (51) to the generalized Darboux–Halphen system, taken in the direction that does not require a diagonalizability argument. The source writes a solution of
--
--   $$\dot M = (\operatorname{Adj} M)^{T} + M^{T}M - (\operatorname{Tr} M)M$$
--
--   as $M = P(d+a)P^{-1}$, where $d = \operatorname{diag}(\omega_1,\omega_2,\omega_3)$, $a$ is the skew-symmetric matrix with $a_{12} = \tau_3$, $a_{23} = \tau_1$, $a_{31} = \tau_2$, and $P$ is a complex orthogonal matrix satisfying the linear equation $\dot P + Pa = 0$, equation (54). This milestone asserts that this recipe does produce a solution: if $(\omega_j,\tau_j)$ solve (52)–(53) and $P$ solves (54) and is complex orthogonal, then $M = P(d+a)P^{T}$ solves (51).
--
--   Orthogonality of $P$ is what makes the argument work and is not cosmetic: the right-hand side of (51) involves a transpose, and $M \mapsto (\operatorname{Adj}M)^{T} + M^{T}M - (\operatorname{Tr}M)M$ is equivariant under conjugation by $P$ only when $P^{T} = P^{-1}$.
--
--   **Conventions shared with the rest of the mission.** All functions are complex-valued functions of a complex variable; a system is required to hold only at the points of an arbitrary set $s \subseteq \mathbb{C}$, with no openness, connectedness or holomorphy assumed; and each derivative that a statement mentions is carried by an explicit companion function tied to it by a pointwise differentiability assertion, so no statement ever refers to the value of a derivative that does not exist.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V pp. 3164-3165, Eq. (51), the factorization M = Ms + Ma = P(d+a)P^{-1} with a12 = -a21 = τ3, a23 = -a32 = τ1, a31 = -a13 = τ2, and Eqs. (52)-(54)

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

namespace SDYM

theorem matrix_flow_of_generalized_darboux_halphen
    (s : Set ℂ) (w₁ w₂ w₃ x₁ x₂ x₃ : ℂ → ℂ)
    (A P M : ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (hDH : IsGeneralizedDHSolution s w₁ w₂ w₃ x₁ x₂ x₃)
    (hA : ∀ t : ℂ, A t = !![0, x₃ t, -x₂ t; -x₃ t, 0, x₁ t; x₂ t, -x₁ t, 0])
    (hPorth : ∀ t ∈ s, (P t).transpose * P t = 1)
    (hP : ∀ t ∈ s, ∀ i j, HasDerivAt (fun z => P z i j) ((-(P t * A t)) i j) t)
    (hM : ∀ t : ℂ, M t = P t * (Matrix.diagonal ![w₁ t, w₂ t, w₃ t] + A t) * (P t).transpose) :
    ∀ t ∈ s, ∀ i j, HasDerivAt (fun z => M z i j)
      (((M t).adjugate.transpose + (M t).transpose * M t
        - Matrix.trace (M t) • M t) i j) t := by sorry

end SDYM
