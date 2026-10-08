-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_greedy_moved_compare
-- name    : SchrijverSFM.Alg.greedy_moved_compare
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:07.437286+00:00
-- url     : https://prove2.me/theorems/ff4ecd87-8dd9-4518-b11f-28116f32b3ff
-- title:
--   Display (8), §3, pp. 349–350 — comparison of h^{≺^{s,u}} with h^≺
-- statement:
--   Let $f$ be a submodular real function on the subsets of $V = \{0, \dots, n-1\}$, let $\prec$ be a total order on $V$, let $s, u \in V$ with $s \prec u$, and let $\prec^{s,u}$ be the order obtained from $\prec$ by moving $u$ to the position just before $s$. Then for each $v \in V$:
--   $$
--   \begin{aligned}
--   h^{\prec^{s,u}}(v) &\le h^{\prec}(v) && \text{if } s \preceq v \prec u,\\
--   h^{\prec^{s,u}}(v) &\ge h^{\prec}(v) && \text{if } v = u,\\
--   h^{\prec^{s,u}}(v) &= h^{\prec}(v) && \text{otherwise.}
--   \end{aligned}
--   $$
--
--   This sign pattern determines the shape of the matrix whose rows are the vectors $h^{\prec^{s,u}}$, $u \in (s,t]_\prec$, and is the input to the subroutine (12).
--
--   **Formalization Note** The moved order is any permutation $\tau$ satisfying the relational characterization `IsMoved σ s u τ` of the setting file. The paper's normalization $f(\emptyset) = 0$ is not needed and is not assumed.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), pp. 349–350, display (8)

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem greedy_moved_compare {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (σ : Equiv.Perm (Fin n)) (s u : Fin n) (hsu : σ s < σ u)
    (τ : Equiv.Perm (Fin n)) (hτ : IsMoved σ s u τ) :
    ∀ v : Fin n,
      (σ s ≤ σ v ∧ σ v < σ u → greedy f τ v ≤ greedy f σ v) ∧
      (v = u → greedy f σ v ≤ greedy f τ v) ∧
      (v ≠ u → ¬ (σ s ≤ σ v ∧ σ v < σ u) → greedy f τ v = greedy f σ v) := by sorry
end SchrijverSFM.Alg
