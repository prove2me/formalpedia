-- Prove2me | Theorems.Thm_SumOfCubesPractice_triangleSum_sq_succ
-- name    : SumOfCubesPractice.triangleSum_sq_succ
-- status  : Proved
-- author  : @hacv16
-- created : 2026-10-16T14:57:47.407462+00:00
-- url     : https://prove2.me/theorems/5f770ea8-3f30-45be-a487-fb6e66cb2a4f
-- title:
--   Milestone 2: Successive triangular squares
-- statement:
--   Let $n$ be any natural number, including zero, and let $\operatorname{triangleSum}(m)=\sum_{k=1}^{m}k$ for every natural number $m$. Then $$\operatorname{triangleSum}(n+1)^2=\operatorname{triangleSum}(n)^2+(n+1)^3.$$ This specifies the increment in the square of the triangular sum between consecutive inputs.
-- source:
--   Requester-supplied mathematical statement for Sum of Cubes Identity (Practice); no external bibliographic source supplied. Milestone 2.

import Definitions.Def_SumOfCubesPractice_triangleSum

namespace SumOfCubesPractice

theorem triangleSum_sq_succ (n : ℕ) :
    triangleSum (n + 1) ^ 2 = triangleSum n ^ 2 + (n + 1) ^ 3 := by sorry

end SumOfCubesPractice
