-- Prove2me | Theorems.Thm_UhlmannRoof_RankTwo_corollary_10
-- name    : UhlmannRoof.RankTwo.corollary_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:19.139893+00:00
-- url     : https://prove2.me/theorems/4ac57c82-1729-4bf4-a69b-9de7bbd9d55f
-- title:
--   Corollary, p. 7, equation (10) — the intersection of supporting contact sets
-- statement:
--   For a state $\omega$, intersect all the contact sets of supporting affine functionals that touch $R$ at $\omega$, and call the result $\Omega_\omega$. Then $\Omega_\omega$ is compact and convex, it contains every pure state appearing in an optimal decomposition of $\omega$, and $R$ is affine on it:
--   $$R(tx+(1-t)y)=tR(x)+(1-t)R(y)\quad(x,y\in\Omega_\omega,\ 0\le t\le1).$$
--   The set $\Omega_\omega$ is the one appearing in Lemma 6; it is the full intersection of contact sets, regardless of whether a point appears in an optimal decomposition.
-- source:
--   Uhlmann, arXiv:quant-ph/9704017v2, p. 7, Corollary and eq. (10)

import Mathlib
import Definitions.Def_UhlmannRoof_RankTwo_Model

namespace UhlmannRoof.RankTwo

/-- Uhlmann, Corollary, p. 7, equation (10): the intersection of all
supporting contact sets at a state is compact and convex, contains every
pure state from an optimal decomposition, and is affine for R. -/
theorem corollary_10 {d : ℕ} (ω : Mat d) (hω : IsState ω) :
    Convex ℝ (OmegaOf ω) ∧ IsCompact (OmegaOf ω) ∧
    (∀ (m : ℕ) (p : Fin m → ℝ) (ρ : Fin m → Mat d),
      IsOptimalDecomp ω p ρ → ∀ k, ρ k ∈ OmegaOf ω) ∧
    (∀ x ∈ OmegaOf ω, ∀ y ∈ OmegaOf ω, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      R (t • x + (1 - t) • y) = t * R x + (1 - t) * R y) := by sorry

end UhlmannRoof.RankTwo
