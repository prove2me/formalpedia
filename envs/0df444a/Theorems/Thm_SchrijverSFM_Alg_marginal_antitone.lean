-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_marginal_antitone
-- name    : SchrijverSFM.Alg.marginal_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:38.996325+00:00
-- url     : https://prove2.me/theorems/f9438c32-0e79-4573-b932-d9a667cc5f90
-- title:
--   Display (9), §3, p. 349 — diminishing marginal values: f(Y ∪ {v}) − f(Y) ≤ f(X ∪ {v}) − f(X)
-- statement:
--   Let $V = \{0, \dots, n-1\}$ and let $f$ be a submodular real function on the subsets of $V$, i.e. $f(Y) + f(Z) \ge f(Y \cap Z) + f(Y \cup Z)$ for all $Y, Z \subseteq V$. If $X \subseteq Y \subseteq V$ and $v \in V \setminus Y$, then
--   $$f(Y \cup \{v\}) - f(Y) \le f(X \cup \{v\}) - f(X).$$
--
--   The marginal value of adding an element can only decrease as the set grows. In the paper this inequality is the tool behind the comparison (8) of the greedy vectors of an order and of a moved order.
--
--   **Formalization Note** The normalization $f(\emptyset) = 0$ of the paper is not needed here and is not assumed.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 349, display (9)

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem marginal_antitone {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) :
    ∀ X Y : Finset (Fin n), X ⊆ Y → ∀ v : Fin n, v ∉ Y →
      f (insert v Y) - f Y ≤ f (insert v X) - f X := by sorry
end SchrijverSFM.Alg
