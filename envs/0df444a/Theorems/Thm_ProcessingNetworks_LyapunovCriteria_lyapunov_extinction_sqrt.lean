-- Prove2me | Theorems.Thm_ProcessingNetworks_LyapunovCriteria_lyapunov_extinction_sqrt
-- name    : ProcessingNetworks.LyapunovCriteria.lyapunov_extinction_sqrt
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:58:29.057659+00:00
-- url     : https://prove2.me/theorems/90890084-b888-4bf9-a3ce-53c711801653
-- title:
--   Lemma 8.6 — Lyapunov extinction criterion, square-root drift bound (milestone)
-- statement:
--   **Lemma 8.6.** In the setting of Lemma 8.5, if instead there is $\varepsilon > 0$ with
--   $\dot f(t) \le -\varepsilon\sqrt{f(t)}$ for almost every $t$ with $Z(t) \ne 0$, then
--   $Z(t) = 0$ for $t \ge t_0 := \sqrt{f(0)}/\varepsilon$.
--
--   This variant is useful exactly when $H$ is quadratic (so $\sqrt{H}$, not $H$ itself, has a
--   controllable linear-in-$t$ decrease) — the natural Lyapunov function for a Euclidean-norm-type
--   drift bound.
--
--   **Formalization note.** Same hypothesis pattern on $H$ as Lemma 8.5 (Lipschitz,
--   positive-definite), and the same standing assumption `hA`, `hAcol` on the capacity consumption
--   matrix; the drift bound is $d \le -\varepsilon\sqrt{H(Z(t))}$ instead of
--   $d \le -\varepsilon$, and the conclusion's threshold is $\sqrt{H(Z(0))}/\varepsilon$ instead
--   of $H(Z(0))/\varepsilon$, matching (8.4)-(8.5) exactly.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 137, Lemma 8.6

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_LipschitzOn
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData

namespace ProcessingNetworks.LyapunovCriteria

open MeasureTheory

/-- Lemma 8.6, Dai & Harrison p. 137 (PDF p. 153): in the setting of Lemma 8.5, with `f` again
defined by `f(t) := H(Z(t))`, if there is `ε > 0` such that `ḟ(t) ≤ -ε√f(t)` for almost all `t`
with `Z(t) ≠ 0` (8.4), then `Z(t) = 0` for `t ≥ t₀ = √(f(0))/ε`. -/
theorem lyapunov_extinction_sqrt
    {I : ℕ} (H : (Fin I → ℝ) → ℝ)
    (hH_lip : IsLipschitzOn H {z : Fin I → ℝ | ∀ i, 0 ≤ z i})
    (hH0 : H (fun _ => 0) = 0) (hHpos : ∀ z : Fin I → ℝ, z ≠ (fun _ => 0) → H z ≠ 0)
    {J K : ℕ} (dat : FluidEquationData I J K)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat Dh Fh Th Zh)
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → Zh t ≠ (fun _ => 0) →
      ∀ d : ℝ, HasDerivAt (fun s => H (Zh s)) d t → d ≤ -ε * Real.sqrt (H (Zh t))) :
    ∀ t : ℝ, Real.sqrt (H (Zh 0)) / ε ≤ t → Zh t = fun _ => 0 := by sorry

end ProcessingNetworks.LyapunovCriteria
