-- Prove2me | Theorems.Thm_SilverRateLB_footnote_6_rescaling
-- name    : SilverRateLB.footnote_6_rescaling
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:21:53.452034+00:00
-- url     : https://prove2.me/theorems/c5289a4a-e61e-4967-a13d-7edd7cb77d5c
-- title:
--   Footnote 6 — rescaling $f\mapsto f/L$, $h_t\mapsto Lh_t$ reduces to $L=1$
-- statement:
--   For every $L>0$ and every stepsize schedule $H=(h_1,\dots,h_n)$,
--   $$\mathscr R_n^{(L)}(H)=\mathscr R_n^{(1)}(LH),$$
--   where $\mathscr R_n^{(L)}$ is the worst-case normalized suboptimality (1) over convex $L$-smooth functions and $LH=(Lh_1,\dots,Lh_n)$. Replacing $f$ by $f/L$ and each $h_t$ by $Lh_t$ preserves the iterates and the normalized function suboptimality.
--
--   This is what allows the paper to work with $L=1$ throughout Sections 2–3 and the proofs.
--
--   Differences from the source:
--   - encoding: “preserves the iterates and normalized function suboptimality” → worstCaseRate L H = worstCaseRate 1 (H.map (L * ·)); reason: the supremum (1) ranges over the bijective image f ↦ f/L of the function class
--   - generalization: nonnegative schedules (the paper's setting) → every real schedule; reason: the rescaling does not use the sign of the stepsizes; nonnegative schedules are instances
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), footnote 6, p. 6

import Mathlib
import Definitions.Def_SilverRateLB_worstCaseRate

namespace SilverRateLB

/-- **Footnote 6 (rescaling to `L = 1`).** Replacing `f` by `f/L` and each `h_t` by `L h_t`
preserves the iterates and the normalized function suboptimality, so
`ℛ_n(H)` for `L`-smooth functions equals `ℛ_n(L H)` for `1`-smooth functions.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, footnote 6, p. 6.

**Formalization Note** Stated for every real schedule `H` (the bijection `f ↦ f/L` does not use
the sign of the stepsizes); the paper applies it to nonnegative schedules. -/
theorem footnote_6_rescaling (L : ℝ) (hL : 0 < L) (H : List ℝ) :
    worstCaseRate L H = worstCaseRate 1 (H.map (fun h => L * h)) := by sorry

end SilverRateLB
