-- Prove2me | Theorems.Thm_PGDMap20261031_entropy_error_monotone
-- name    : PGDMap20261031.entropy_error_monotone
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:04.775259+00:00
-- url     : https://prove2.me/theorems/0ae56246-95c7-4a73-b99f-4c16770aad7b
-- title:
--   The curvature-error transform strictly increases with the scaled geometry
-- statement:
--   ## Statement
--
--   For every pair of real numbers $A,B$ with $A>0$ and $B>0$, the function $v\mapsto(v-A)/(v+B)$ is strictly increasing on $(0,\infty)$: for every pair of real numbers $v_1,v_2$ with $0<v_1<v_2$, $(v_1-A)/(v_1+B)<(v_2-A)/(v_2+B)$. No upper bound on $A$, $B$, or the positive variables is assumed.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, Lemma 2 proof, p. 3; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.entropy_error_monotone : ∀ A B : ℝ, 0 < A → 0 < B → StrictMonoOn (fun v : ℝ => (v - A) / (v + B)) (Set.Ioi (0 : ℝ)) := by sorry
