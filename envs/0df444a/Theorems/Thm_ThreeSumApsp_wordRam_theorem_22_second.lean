-- Prove2me | Theorems.Thm_ThreeSumApsp_wordRam_theorem_22_second
-- name    : ThreeSumApsp.wordRam_theorem_22_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T08:22:06.35932+00:00
-- url     : https://prove2.me/theorems/196a1bec-c186-49fe-b25b-886028722edc
-- title:
--   Theorem 22 — shared 3SUM, min-plus, and APSP bounds
-- statement:
--   For every fixed natural input-magnitude exponent $\kappa$, the following problems on polynomially bounded integer inputs admit deterministic word-RAM algorithms:
--
--   - 3SUM on $n$ integers in $O(n^{1.9992})$ time, accepting exactly when three pairwise distinct positions sum to zero.
--   - The $(\min,+)$-product of two $n\times n$ integer matrices in $O(n^{3-0.00175/3}(\log n)^{e})$ time for some natural $e$ depending on $\kappa$, and in $O(n^{2.99942})$ time.
--   - All-pairs shortest paths on directed $n$-vertex graphs with integer weights and no negative cycles, with both of the same time bounds as the $(\min,+)$-product.
--
--   For each claim, the program, word-width constant, and runtime constant may depend on $\kappa$ but must work for every input size and every sufficiently large logarithmic word width. Correctness and outputs use the shared `EndStatement` specifications.
--
--   This is Anthropic's exact `Items.Theorem_22_second`: the refined part of Theorem 22 using Corollary 26. It is a shared proof dependency for the 3SUM and APSP missions.
-- source:
--   https://arxiv.org/abs/2610.06783v1; Theorem 22, refined bounds using Corollary 26; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L3901-L3910

import Definitions.Def_APSPSource_PaperStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ThreeSumApsp.WordRam

theorem ThreeSumApsp.wordRam_theorem_22_second :
    ThreeSumApsp.WordRam.SolvedInTime EndStatement.ThreeSum 1.9992 0 ∧
  ThreeSumApsp.WordRam.SolvedInPolylogTime EndStatement.MinPlusProduct (3 - 175e-5 / 3) ∧
    ThreeSumApsp.WordRam.SolvedInPolylogTime EndStatement.APSP (3 - 175e-5 / 3) ∧
      ThreeSumApsp.WordRam.SolvedInTime EndStatement.MinPlusProduct 2.99942 0 ∧
        ThreeSumApsp.WordRam.SolvedInTime EndStatement.APSP 2.99942 0 := by sorry
