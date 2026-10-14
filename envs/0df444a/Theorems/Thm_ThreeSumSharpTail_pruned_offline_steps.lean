-- Prove2me | Theorems.Thm_ThreeSumSharpTail_pruned_offline_steps
-- name    : ThreeSumSharpTail.pruned_offline_steps
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T18:37:18.72165+00:00
-- url     : https://prove2.me/theorems/12a2aa24-6365-42c3-8835-5550f7ef729e
-- title:
--   Uniform bound for the actual pruned offline routine step count
-- statement:
--   For every rational parameter record G, nonnegative cost constant C, and fixed setup constants c0,k, there is a uniform constant A such that CostsWithinP(G,C,N,D,Tp,Tq) implies tOffline32P(c0,G,N,D,w)+k <= A(Tp+w Tq) for every number w of queries. The natural step-count function includes preprocessing, parameter setup and the complete query loop. No additional asymptotic cost hypothesis is assumed.
-- source:
--   Reusable generic cost proof from the ACCEPTED TrulySubquadratic3SUM.exactTriangleUniform_9261_5000000 source, submission 45d9b962-dd72-4a1f-a54c-8186be3ae4ec, ThreeSumApsp/Pruned/CostsP.lean at source commit 27a2fa4bab32. Actual enumeration and time-function proof bodies are included; the existing proved enumeration/order statements are reused.

import Definitions.Def_APSP299791_Defs4

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.pruned_offline_steps (G : Light.Sec4.RatParams)
    (C : ℝ) (hC : 0 ≤ C) (c0 k : ℕ) :
    ∃ A : ℝ, ∀ N D : ℕ, ∀ tp tq : ℝ, ∀ w : ℕ,
      Light.Sec4.CostsWithinP G C N D tp tq →
        (Light.Sec4.tOffline32P c0 G N D w : ℝ) + (k : ℝ) ≤ A * (tp + (w : ℝ) * tq) := by sorry
