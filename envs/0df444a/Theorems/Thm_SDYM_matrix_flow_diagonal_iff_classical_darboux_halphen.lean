-- Prove2me | Theorems.Thm_SDYM_matrix_flow_diagonal_iff_classical_darboux_halphen
-- name    : SDYM.matrix_flow_diagonal_iff_classical_darboux_halphen
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T01:27:03.821298+00:00
-- url     : https://prove2.me/theorems/884da552-5d9a-40b3-9590-7cbac088832d
-- title:
--   The matrix flow (51) for diagonal $M$ is the classical Darboux–Halphen system
-- statement:
--   The matrix flow obtained by reducing the Nahm equations with the gauge algebra of divergence-free vector fields on $S^3$ is
--
--   $$\dot M = (\operatorname{Adj} M)^{T} + M^{T}M - (\operatorname{Tr} M)M,\qquad \operatorname{Adj} M = (\det M)M^{-1},$$
--
--   equation (51) of the source. This milestone identifies its diagonal sector: if $M = \operatorname{diag}(\omega_1,\omega_2,\omega_3)$ then the flow holds if and only if $\omega_1,\omega_2,\omega_3$ solve the classical Darboux–Halphen system. It is the base case of the general factorization $M = P(d+a)P^{-1}$ — the case $P = I$, $a = 0$ — and it fixes the normalization of the matrix equation against the first-order system.
--
--   The matrix derivative is imposed entrywise, so that no normed-space structure on $3\times3$ matrices has to be chosen; the adjugate is the classical adjugate, defined for every matrix without an invertibility hypothesis.
--
--   **Conventions shared with the rest of the mission.** All functions are complex-valued functions of a complex variable; a system is required to hold only at the points of an arbitrary set $s \subseteq \mathbb{C}$, with no openness, connectedness or holomorphy assumed; and each derivative that a statement mentions is carried by an explicit companion function tied to it by a pointwise differentiability assertion, so no statement ever refers to the value of a derivative that does not exist.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V pp. 3164-3165, Eq. (51) and Eq. (52) with τ = 0

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

namespace SDYM

theorem matrix_flow_diagonal_iff_classical_darboux_halphen
    (s : Set ℂ) (w₁ w₂ w₃ : ℂ → ℂ) (M : ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (hM : ∀ t : ℂ, M t = Matrix.diagonal ![w₁ t, w₂ t, w₃ t]) :
    ((∀ t ∈ s, ∀ i j, HasDerivAt (fun z => M z i j)
        (((M t).adjugate.transpose + (M t).transpose * M t
          - Matrix.trace (M t) • M t) i j) t)
      ↔ IsClassicalDHSolution s w₁ w₂ w₃) := by sorry

end SDYM
