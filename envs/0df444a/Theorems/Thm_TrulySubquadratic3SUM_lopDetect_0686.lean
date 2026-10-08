-- Prove2me | Theorems.Thm_TrulySubquadratic3SUM_lopDetect_0686
-- name    : TrulySubquadratic3SUM.lopDetect_0686
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-06T19:05:20.917236+00:00
-- url     : https://prove2.me/theorems/0b5dd2ed-3f96-4b1e-8dcb-7a9f46615820
-- title:
--   Lopsided triangle detection with saving $0.0686$
-- statement:
--   There exist a real constant $C\ge0$ and a time function $T:\mathbb N^3\to\mathbb R$ for a correct deterministic procedure that reports, for every queried vertex pair in a lopsided tripartite graph, whether the pair has a common neighbor. The procedure satisfies the existing Light word-RAM model and its polynomial resource requirements, and for all natural $n,D$ with $D\ge1$ and $D^{500}\le n^{27}$, $T(n,D,\lfloor n^2/\sqrt D\rfloor)\le C n^2/D^{0.0686}$. The same procedure, $C$ and $T$ work throughout this range. This is an open algorithmic target.
-- source:
--   Open parameter-refinement target inspired by Alman and Vassilevska Williams (2026), using the existing Anthropic formal-math source at commit e1a4e6508154ea59f030480661590a9fe3018011. This target is proposed here, not asserted as a proved result of the paper. Generic inner construction: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean. Parameter estimates: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Table2.lean.

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubquadratic3SUM.lopDetect_0686 :
    ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ),
      0 ≤ C ∧ Light.lightModel.lopDetect T ∧
      ∀ n D, 1 ≤ D → D ^ 500 ≤ n ^ 27 →
        T n D (ThreeSumApsp.queryCap n D) ≤
          C * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.0686 : ℝ)) := by sorry
