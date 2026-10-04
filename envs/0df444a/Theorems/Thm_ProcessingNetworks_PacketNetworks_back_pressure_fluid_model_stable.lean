-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_back_pressure_fluid_model_stable
-- name    : ProcessingNetworks.PacketNetworks.back_pressure_fluid_model_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:58:00.244798+00:00
-- url     : https://prove2.me/theorems/b9ef17f4-44dd-4227-b9db-732511c12aa2
-- title:
--   Lemma 12.21 — the back-pressure fluid model is stable under (12.26) (milestone)
-- statement:
--   **Lemma 12.21.** If (12.26) is satisfied, then the fluid model defined by (12.31)-(12.36) and
--   (12.44) is stable.
--
--   The book's own proof is "almost identical to that of Theorem 9.12" (mission VIII): a quadratic
--   Lyapunov function $g(t) := \hat Z(t)\cdot\hat Z(t)$ has strictly negative drift bounded away
--   from $0$ whenever $\hat Z(t)\ne 0$, using exactly the strict inequality $\lambda < R\hat s$ of
--   (12.26).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 243, Lemma 12.21

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPFluidModel

namespace ProcessingNetworks.PacketNetworks

/-- Lemma 12.21, Dai & Harrison p. 243 (PDF p. 259): if (12.26) is satisfied (`λ < Rŝ` for some
`ŝ ∈ ⟨S⟩`), then the fluid model defined by equations (12.31)-(12.36) and (12.44) is stable: there
is a `δ > 0` such that every fluid model solution has `Ẑ(t) = 0` for all `t ≥ δ`. -/
theorem back_pressure_fluid_model_stable
    {I J : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ)) (lam : Fin I → ℝ)
    (hload : ∃ shat ∈ hullFinset S, ∀ i, lam i < (R dat).mulVec shat i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ),
      IsBackPressureFluidModelSolution dat S lam Dh Th Zh →
      ∀ t : ℝ, δ ≤ t → Zh t = fun _ => 0 := by sorry

end ProcessingNetworks.PacketNetworks
