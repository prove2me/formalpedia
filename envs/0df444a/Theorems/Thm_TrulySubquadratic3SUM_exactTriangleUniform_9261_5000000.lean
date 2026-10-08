-- Prove2me | Theorems.Thm_TrulySubquadratic3SUM_exactTriangleUniform_9261_5000000
-- name    : TrulySubquadratic3SUM.exactTriangleUniform_9261_5000000
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T19:05:36.366824+00:00
-- url     : https://prove2.me/theorems/80496bcf-f80d-4dab-8fec-0a675bc025e6
-- title:
--   Uniform Exact Triangle saving $9261/5000000$
-- statement:
--   There exist a real constant $K\ge1$ and a single deterministic program in the Light word-RAM model, with polynomially bounded resource needs, that decides whether an integer-weighted complete tripartite graph with $s$ vertices in each part has a triangle whose three edge weights sum to zero. For every natural $s\ge1$, natural weight bound $U\ge1$, and real $u\ge U$, its time on instances with absolute edge weights at most $U$ is at most $K s^{3-9261/5000000}(\log s+1)(1+\log(\max\{2,u\}))^2$, with natural logarithms. This is an open algorithmic target.
-- source:
--   Open parameter-refinement target inspired by Alman and Vassilevska Williams (2026), using the existing Anthropic formal-math source at commit e1a4e6508154ea59f030480661590a9fe3018011. This target is proposed here, not asserted as a proved result of the paper. Generic inner construction: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean. Parameter estimates: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Table2.lean.

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubquadratic3SUM.exactTriangleUniform_9261_5000000 :
    ThreeSumApsp.Claim.ExactTriangleUniform Light.lightModel (9261 / 5000000) 1 := by sorry
