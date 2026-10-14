-- Prove2me | Theorems.Thm_ThreeSumSharpTail_pruned_program_correct
-- name    : ThreeSumSharpTail.pruned_program_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T18:02:43.769078+00:00
-- url     : https://prove2.me/theorems/765788f5-2182-4f3d-881f-3a88a041c891
-- title:
--   Pruned offline program correctness for arbitrary rational parameters
-- statement:
--   For every finite rational parameter record G, the published program31P(G) satisfies OfflineSpec32P at every machine limit. It executes the specified preprocessing and queries on the actual stored matrices and selected entries, with the declared step counts. This is the generic correctness interface of the pruned program; asymptotic cost regimes, word-size polynomial bounds and the 3SUM reduction are separate conclusions.
-- source:
--   Reusable generic portion of the ACCEPTED proof of Light.Sec4.allInstancesP_programP, submission 50de6837-5a9a-4f1f-ab1f-e9cff8fc270a. ThreeSumApsp/Pruned/Program31P.lean and related choosing-parameter specifications at formal-math commit 27a2fa4bab32. The preprocessing, query and offline procedure proofs are generic in G; the later fixed-parameter wrapper is excluded.

import Definitions.Def_APSP299791_Defs5

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.pruned_program_correct (G : Light.Sec4.RatParams) : ∀ lim,
    Light.Sec4.OfflineSpec32P lim (Light.Sec4.program31P G) Light.Sec4.cShared30 G := by sorry
