-- Prove2me | Theorems.Thm_PlatformPrecommit_KS_lemma_6
-- name    : PlatformPrecommit.KS.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:40.10403+00:00
-- url     : https://prove2.me/theorems/04e483b0-89fa-49eb-8e33-14ebdbbf9189
-- title:
--   Lemma 6, p. 14 — unique symmetric quantity equilibrium and closed forms (10)
-- statement:
--   In the two-platform quantity game with $\Omega>0$ and $0\le\beta,\gamma<1$, there is exactly one Nash equilibrium. It is symmetric. Write $D=4+\beta+\gamma-2\gamma^2-2\beta^2-\beta^2\gamma-\beta\gamma^2$. Every platform has
--
--   $$z_i^*=\frac{(1+\gamma)(1-\beta^2)}{D}\Omega,\quad p_i^*=\frac{3+\beta-\beta^2-2\gamma^2-\beta\gamma^2}{(1-\gamma)D}\Omega,\quad w_i^*=\frac{(1+\gamma)(1+\beta)}{D}\Omega,$$
--
--   and profit
--
--   $$\pi_i^*=\frac{(2-\gamma^2-\beta^2)(1+\gamma)(1-\beta^2)}{(1-\gamma)D^2}\Omega^2.$$
--
--   The result identifies the single-stage outcome to which capacity precommitment is compared.
--
--   **Formalization Note** The equilibrium quantifies over every nonnegative quantity profile, without a symmetry restriction. The market-clearing inverse price and wage are those derived in the proof of Lemma 6, Online Appendix p. 32, (F.3).
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), p. 14, Lemma 6 and (10); Online Appendix p. 32, (F.3)

import Mathlib
import Definitions.Def_PlatformPrecommit_KS_Setting

namespace PlatformPrecommit.KS

/-- Lemma 6, p. 14: the unique quantity equilibrium and its four closed forms. -/
theorem lemma_6 (M : Model) (hM : M.Standing) :
    let D : ℝ := 4 + M.β + M.γ - 2 * M.γ ^ 2 - 2 * M.β ^ 2 -
      M.β ^ 2 * M.γ - M.β * M.γ ^ 2
    let pQ : ℝ := (3 + M.β - M.β ^ 2 - 2 * M.γ ^ 2 - M.β * M.γ ^ 2) /
      ((1 - M.γ) * D) * M.Ω
    let wQ : ℝ := ((1 + M.γ) * (1 + M.β)) / D * M.Ω
    let zQ : ℝ := ((1 + M.γ) * (1 - M.β ^ 2)) / D * M.Ω
    let πQ : ℝ := ((2 - M.γ ^ 2 - M.β ^ 2) * (1 + M.γ) * (1 - M.β ^ 2)) /
      ((1 - M.γ) * D ^ 2) * M.Ω ^ 2
    (∃! z : Fin 2 → ℝ, M.IsQNE z) ∧
      ∀ z, M.IsQNE z → ∀ i : Fin 2,
        z i = zQ ∧ M.qPrice z i = pQ ∧ M.qWage z i = wQ ∧ M.qProfit z i = πQ := by sorry

end PlatformPrecommit.KS
