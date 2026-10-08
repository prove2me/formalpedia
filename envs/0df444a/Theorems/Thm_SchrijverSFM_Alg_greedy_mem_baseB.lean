-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_greedy_mem_baseB
-- name    : SchrijverSFM.Alg.greedy_mem_baseB
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:48.94049+00:00
-- url     : https://prove2.me/theorems/798b2dd7-cc2d-411f-b54b-3ca0d3a8d831
-- title:
--   §2, pp. 348–349 — h^≺(U) = f(U) for every lower ideal U of ≺, and h^≺ ∈ B_f
-- statement:
--   Let $V = \{0, \dots, n-1\}$, let $f$ be a submodular real function on the subsets of $V$ with $f(\emptyset) = 0$, and let $\prec$ be a total order on $V$ with greedy vector $h^\prec(v) = f(v_\prec \cup \{v\}) - f(v_\prec)$, where $v_\prec = \{u \mid u \prec v\}$. Then
--   1. $h^\prec(U) = f(U)$ for every lower ideal $U$ of $\prec$ (a set with $u \in U,\ w \prec u \Rightarrow w \in U$), where $h^\prec(U) = \sum_{v \in U} h^\prec(v)$;
--   2. $h^\prec$ belongs to the base polytope:
--   $$h^\prec(U) \le f(U) \ \text{ for all } U \subseteq V, \qquad h^\prec(V) = f(V).$$
--
--   Every greedy vector is therefore a point of $B_f$, so every convex combination of greedy vectors, which is how the algorithm stores its current point, lies in $B_f$. The identity on lower ideals is what makes the Case 1 set a minimizer.
--
--   **Formalization Note** A total order is a permutation $\sigma$ of `Fin n` read as a position map ($u \prec v$ iff $\sigma(u) < \sigma(v)$).
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 348 (§2, sentence after display (6)) and pp. 348–349 (§2, last paragraph)

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem greedy_mem_baseB {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) (σ : Equiv.Perm (Fin n)) :
    (∀ U : Finset (Fin n), IsLowerIdeal σ U → xsum (greedy f σ) U = f U) ∧
      greedy f σ ∈ baseB f := by sorry
end SchrijverSFM.Alg
