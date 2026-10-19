-- Prove2me | Theorems.Thm_SumOfCubesPractice_cubeSum_eq_triangleSum_sq
-- name    : SumOfCubesPractice.cubeSum_eq_triangleSum_sq
-- status  : Proved
-- author  : @hacv16
-- created : 2026-10-16T14:58:00.547321+00:00
-- url     : https://prove2.me/theorems/3988d10d-1c06-4aae-b69d-984dd475bf92
-- title:
--   Sum of cubes identity
-- statement:
--   For every natural number $n$, including zero, the sum of the cubes of the first $n$ positive integers equals the square of their sum: $$\operatorname{cubeSum}(n)=\operatorname{triangleSum}(n)^2,$$ where $\operatorname{cubeSum}(n)=\sum_{k=1}^{n}k^3$ and $\operatorname{triangleSum}(n)=\sum_{k=1}^{n}k$. Empty sums have value zero. This is the main identity of the practice mission.
-- source:
--   Requester-supplied mathematical statement for Sum of Cubes Identity (Practice); no external bibliographic source supplied. Final goal.

import Definitions.Def_SumOfCubesPractice_triangleSum
import Definitions.Def_SumOfCubesPractice_cubeSum

namespace SumOfCubesPractice

theorem cubeSum_eq_triangleSum_sq (n : ℕ) :
    cubeSum n = triangleSum n ^ 2 := by sorry

end SumOfCubesPractice
