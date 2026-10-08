-- Prove2me | Theorems.Thm_Research_uniform_refined
-- name    : Research.uniform_refined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T18:47:36.739817+00:00
-- url     : https://prove2.me/theorems/9eeece5d-48d5-46d7-97ea-417ca5a0054b
-- title:
--   Uniform Exact Triangle saving 2/1125
-- statement:
--   There exist a constant K >= 1 and a single deterministic program in the Light word-RAM model that decides whether an integer-weighted complete tripartite graph with s vertices in each part has a triangle whose three edge weights sum to zero. The program has polynomially bounded resource needs. For every natural number s >= 1, every natural-number weight bound U >= 1, and every real u >= U, its running time on instances with absolute edge weights at most U is at most K s^(3 - 2/1125) (log s + 1) (1 + log(max{2,u}))^2, where log is the natural logarithm.
-- source:
--   Parameter refinement of https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSumApsp

theorem Research.uniform_refined : Claim.ExactTriangleUniform Light.lightModel (2 / 1125) 1 := by sorry
