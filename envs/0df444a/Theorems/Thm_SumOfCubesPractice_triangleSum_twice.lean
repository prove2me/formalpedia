-- Prove2me | Theorems.Thm_SumOfCubesPractice_triangleSum_twice
-- name    : SumOfCubesPractice.triangleSum_twice
-- status  : Proved
-- author  : @hacv16
-- created : 2026-10-16T14:57:36.864732+00:00
-- url     : https://prove2.me/theorems/56da2a46-bfa3-465d-9289-9c6eb2d97cce
-- title:
--   Milestone 1: Twice the triangular sum
-- statement:
--   Let $n$ be any natural number, including zero, and let $\operatorname{triangleSum}(n)=\sum_{k=1}^{n}k$. Then $$2\operatorname{triangleSum}(n)=n(n+1).$$ This gives a multiplication-only expression for twice the triangular sum.
-- source:
--   Requester-supplied mathematical statement for Sum of Cubes Identity (Practice); no external bibliographic source supplied. Milestone 1.

import Definitions.Def_SumOfCubesPractice_triangleSum

namespace SumOfCubesPractice

theorem triangleSum_twice (n : ℕ) :
    2 * triangleSum n = n * (n + 1) := by sorry

end SumOfCubesPractice
