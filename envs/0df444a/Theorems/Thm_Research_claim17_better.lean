-- Prove2me | Theorems.Thm_Research_claim17_better
-- name    : Research.claim17_better
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T18:39:23.260982+00:00
-- url     : https://prove2.me/theorems/056a65d6-1854-4273-86cf-7e2ceff3d726
-- title:
--   Exact Triangle grouping with exponent 0.032
-- statement:
--   Keep $D=\lfloor n^{1/18}\rfloor$ and set $g=\lceil D^{0.032}\rceil$. The grouping procedure computes the least natural $g$ with $g^{125}\ge D^4$. There is a constant $C\ge0$ such that every correct deterministic lopsided-triangle solver with time $T(n,D,w)$ yields a correct deterministic Exact Triangle solver with time $T′(n,u)$. Whenever $16\le D\le n$, $1\le g\le\sqrt D$, $\kappa\ge1$, and $u\le n^\kappa$, the new solver satisfies
--   $$T′(n,u)\le4ng\bigl(T(n,D,\lfloor n^2/\sqrt D\rfloor)+Cn^2/\sqrt D\bigr)+C\bigl(\kappa n^3\log n/g+n^{\log_2 7}D^{3/2}+n^2Dg\bigr).$$
--   The same $C$ works for every supplied solver and every permitted input parameter. This refines the grouping parameter in the existing verified light-language implementation; the shared problem and machine definitions remain unchanged.
-- source:
--   Parameter refinement of the original g = ceil(D^0.0315) implementation to g = ceil(D^(4/125)): https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSumApsp

theorem Research.claim17_better :
    Claim.Theorem_17 Light.lightModel strassen paramD₂₆
      (fun n => ⌈(paramD₂₆ n : ℝ) ^ (0.032 : ℝ)⌉₊) := by sorry
