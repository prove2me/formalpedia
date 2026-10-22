-- Prove2me | Theorems.Thm_UhlmannRoof_RankTwo_lemma_2
-- name    : UhlmannRoof.RankTwo.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:32.282913+00:00
-- url     : https://prove2.me/theorems/9c0936c3-1c73-41d6-948a-a64bf2edb890
-- title:
--   Lemma 2, p. 5 — comparison with the convex roof on an R-set
-- statement:
--   Let $S$ be an $R$-set and $F$ a convex real function on $S$. Suppose $F(\rho)\le R(\rho)$ for every pure state $\rho$ in $S$. Then
--   $$F(\omega)\le R(\omega)\qquad(\omega\in S).$$
--   Thus comparison of a convex function with the convex roof can be reduced to the pure states of an $R$-set.
-- source:
--   Uhlmann, arXiv:quant-ph/9704017v2, p. 5, Lemma 2

import Mathlib
import Definitions.Def_UhlmannRoof_RankTwo_Model

namespace UhlmannRoof.RankTwo

/-- Uhlmann, Lemma 2, p. 5: comparison of a convex function with the roof
on an R-set can be checked on the pure states in that set. -/
theorem lemma_2 {d : ℕ} (S : Set (Mat d)) (hS : IsRSet S)
    (F : Mat d → ℝ) (hF : ConvexOn ℝ S F)
    (hpure : ∀ ρ ∈ S, IsPure ρ → F ρ ≤ R ρ) :
    ∀ ω ∈ S, F ω ≤ R ω := by sorry

end UhlmannRoof.RankTwo
