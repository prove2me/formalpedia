-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_dist_monotone
-- name    : SchrijverSFM.Alg.dist_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:06.907978+00:00
-- url     : https://prove2.me/theorems/39c51660-7a40-4e02-b64c-168823b9cb13
-- title:
--   Display (20), §5, pp. 352–353 — distances never decrease: d′(v) ≥ d(v) for all v
-- statement:
--   Let $S \to S'$ be one iteration of the algorithm, and let $d$ and $d'$ be the distance functions of $S$ and $S'$: $d(v)$ is the minimum number of arcs of a directed path in $D$ from $P = \{x > 0\}$ to $v$, and $\infty$ if there is none. Then
--   $$d'(v) \ge d(v) \qquad \text{for all } v \in V.$$
--
--   Together with (21), this monotonicity drives the $|V|^6$ bound: each $d(v)$ can increase at most $|V|$ times.
--
--   **Formalization Note** Distances take values in $\mathbb{N} \cup \{\infty\}$ (`ℕ∞`), with $\infty$ for unreachable vertices. No submodularity is needed.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), pp. 352–353, display (20)

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem dist_monotone {n : ℕ} (f : Finset (Fin n) → ℝ)
    (S S' : State n) (t s : Fin n) (i : ℕ) (hstep : StepVia f S S' t s i) :
    ∀ v : Fin n, dist f S v ≤ dist f S' v := by sorry
end SchrijverSFM.Alg
