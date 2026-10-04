-- Prove2me | Theorems.Thm_StarShapedRisk_LawInvariant_robustified_functional_normalized
-- name    : StarShapedRisk.LawInvariant.robustified_functional_normalized
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T12:47:21.837262+00:00
-- url     : https://prove2.me/theorems/b8c865eb-3704-4c1f-bfe4-2a31222eb352
-- title:
--   Normalization of the robustified functional: rho(0) = 0
-- statement:
--   In the robustified-VaR representation of Castagnoli et al. (2022), Theorem 5, the functional rho(X) = inf_g sup_alpha (psi_alpha(X) - g(alpha)) is normalized: rho(0) = 0 when the benchmark family G is nonempty, star-shaped about 0, every member satisfies inf_alpha g(alpha) <= 0, and psi_alpha(0) = 0. Proof: rho(0) = inf_g (-inf_alpha g(alpha)) = -sup_g inf_alpha g(alpha) = 0.

import Mathlib

namespace StarShapedRisk.LawInvariant

/-- Castagnoli et al. (2022), proof of Theorem 5, `(ii) ⇒ (i)` normalization
    step (p. 2647): for a nonempty family `G` of functions on `(0,1)` that is
    star-shaped about `0` and satisfies `⨅ α, g α ≤ 0` in `EReal` for every
    `g ∈ G`, the robustified functional
    `ρ e0 = ⨅ g ∈ G, ⨆ α, (ψ α e0 - g α)` equals `0` whenever `ψ α e0 = 0`
    for the reference element `e0 : E`.
    Proof: `ρ 0 = ⨅ g ∈ G, -(⨅ α, g α) = -⨆ g ∈ G, ⨅ α, g α = 0`:
    the constant-`0` function lies in `G` (star-shaped + nonempty) so the
    supremum is `≥ 0`, and every member has `⨅ α, g α ≤ 0` so it is `≤ 0`. -/
theorem robustified_functional_normalized {E : Type*}
    (ψ : Set.Ioo (0 : ℝ) 1 → E → ℝ)
    (G : Set (Set.Ioo (0 : ℝ) 1 → ℝ))
    (hne : G.Nonempty) (hstar : StarConvex ℝ 0 G)
    (hg0 : ∀ g ∈ G, ⨅ α : Set.Ioo (0 : ℝ) 1, (g α : EReal) ≤ 0)
    (e0 : E)
    (hψ0 : ∀ α, ψ α e0 = 0) :
    (⨅ g ∈ G, ⨆ α : Set.Ioo (0 : ℝ) 1, (((ψ α e0 - g α : ℝ)) : EReal)) = 0 := by
  sorry

end StarShapedRisk.LawInvariant
