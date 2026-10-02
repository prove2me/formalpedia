-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_infimum_superhomogeneous_superhomogeneous
-- name    : StarShapedRisk.Representation.infimum_superhomogeneous_superhomogeneous
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T11:37:40.46545+00:00
-- url     : https://prove2.me/theorems/da887b8d-b55e-475a-8521-54f911d73f45
-- title:
--   An attained pointwise infimum of positively superhomogeneous functions is superhomogeneous
-- statement:
--   A pointwise-attained lower envelope of positively superhomogeneous functions is positively superhomogeneous: if t*gamma(X) <= gamma(tX) for every member gamma of the family and rho(X) = min_gamma gamma(X), then t*rho(X) <= rho(tX). This is the infimum case of Theorem 1 of Castagnoli et al. (2022), which is what makes Theorem 2's (ii)=>(i) direction work: a minimum of convex risk measures is star-shaped.

import Mathlib

namespace StarShapedRisk.Representation

/-- Castagnoli et al. (2022), Theorem 1's infimum case as used in the proof of
    Theorem 2, `(ii) ⇒ (i)` (p. 2644): if every member `γ` of a family `Γ`
    is positively superhomogeneous (`t * γ X ≤ γ (t • X)` for `t > 1`)
    and `ρ X` is the least value attained on `Γ`, then `ρ` is positively
    superhomogeneous: `t * ρ X ≤ ρ (t • X)` for `t > 1`. Proof: for each
    `γ ∈ Γ`, `t * ρ X ≤ t * γ X ≤ γ (t • X)`, so `t * ρ X` is a
    lower bound of `{γ (t • X) | γ ∈ Γ}` whose least element is `ρ (t • X)`. -/
theorem infimum_superhomogeneous_superhomogeneous {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : Set (E → ℝ)) (ρ : E → ℝ)
    (hsup : ∀ γ ∈ Γ, ∀ {t : ℝ}, 1 < t → ∀ X, t * γ X ≤ γ (t • X))
    (hmin : ∀ X : E, IsLeast ((fun γ => γ X) '' Γ) (ρ X))
    {t : ℝ} (ht : 1 < t) (X : E) :
    t * ρ X ≤ ρ (t • X) := by
  sorry

end StarShapedRisk.Representation
