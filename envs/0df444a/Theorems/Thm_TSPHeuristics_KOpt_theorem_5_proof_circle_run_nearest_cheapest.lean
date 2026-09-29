-- Prove2me | Theorems.Thm_TSPHeuristics_KOpt_theorem_5_proof_circle_run_nearest_cheapest
-- name    : TSPHeuristics.KOpt.theorem_5_proof_circle_run_nearest_cheapest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:56:19.630264+00:00
-- url     : https://prove2.me/theorems/08d33bc9-e4ee-4f03-9d4d-cb52a38cd8d8
-- title:
--   Proof of Theorem 5: the subtours $T_i$ and nodes $a_i=i+1$ form a nearest and a cheapest insertion run on the circle
-- statement:
--   Let $n\ge 6$ and consider the circle graph $(N_n,d_n)$ with the subtours $T_1,\dots,T_n$ and nodes $a_i=i+1$ of the proof of Theorem 5. Then:
--
--   1. $T_1=\{a_0\}$ and, for $1\le i<n$, $a_i\notin T_i$ and $T_{i+1}$ is obtained from $T_i$ by inserting $a_i$ at an edge minimizing $d(x,a_i)+d(a_i,y)-d(x,y)$, i.e. $T_{i+1}=\mathrm{TOUR}(T_i,a_i)$, (3.2);
--   2. every $a_i$ is a nearest node to $T_i$ among the nodes outside $T_i$, (4.2);
--   3. every $a_i$ has the least insertion cost among the nodes outside $T_i$, (4.3).
--
--   So the same sequence of subtours is produced both by nearest insertion and by cheapest insertion (with suitable resolution of ties).
--
--   **Formalization Note** Nodes are 0-based: the paper's $a_i=i+1$ is the index $i$ (`circleNode n _ i`). The subtour index is 1-based as printed. The paper writes "no insertion can cost less than 2 and so (4.2) holds"; that sentence proves the cheapest-insertion condition (4.3), and (4.3) is what is stated here. The hypothesis $n\ge 6$ is the paper's: at $n=4$ and $n=5$ the step $T_3\to T_4$ is not a minimizing insertion.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 576, proof of Theorem 5, paragraphs 'Obviously the T_i defined above are tours …' to '… require the assumption n ≧ 6'

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance

namespace TSPHeuristics.KOpt

theorem theorem_5_proof_circle_run_nearest_cheapest (n : ℕ) (hn : 6 ≤ n) :
    TSPHeuristics.Shared.IsInsertionRun (cycDist n) (circleSubtour n) (circleNode n (by omega)) ∧
      TSPHeuristics.Shared.IsNearestRule (cycDist n) (circleSubtour n) (circleNode n (by omega)) ∧
      TSPHeuristics.Shared.IsCheapestRule (cycDist n) (circleSubtour n) (circleNode n (by omega)) := by sorry

end TSPHeuristics.KOpt
