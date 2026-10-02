-- Prove2me | Theorems.Thm_ProcessingNetworks_LyapunovCriteria_lyapunov_extinction_linear
-- name    : ProcessingNetworks.LyapunovCriteria.lyapunov_extinction_linear
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:57:56.280117+00:00
-- url     : https://prove2.me/theorems/53851659-26e2-490d-abe9-942bea945394
-- title:
--   Lemma 8.5 — Lyapunov extinction criterion, linear drift bound (milestone)
-- statement:
--   A **Lyapunov function** for a fluid model is a function $H$ satisfying all the hypotheses of
--   this lemma.
--
--   **Lemma 8.5.** Let $H : \mathbb{R}^I_+ \to \mathbb{R}_+$ be Lipschitz with $H(0)=0$ and
--   $H(z) \ne 0$ for $z \ne 0$. For a fluid model solution $(D,F,T,Z)$, set $f(t) := H(Z(t))$.
--   If there is $\varepsilon > 0$ with $\dot f(t) \le -\varepsilon$ for almost every $t$ with
--   $Z(t) \ne 0$, then $Z(t) = 0$ for $t \ge t_0 := H(Z(0))/\varepsilon$.
--
--   This is the book's basic drift criterion for fluid model stability: a Lyapunov function that
--   decreases at a uniform rate whenever the system is non-empty forces extinction in finite
--   time, uniformly bounded by $H(Z(0))/\varepsilon$ — exactly the $\gamma|Z(0)|$ bound
--   Definition 6.3 asks for.
--
--   **Formalization note.** "$\dot f(t) \le -\varepsilon$ for almost all $t$ with $Z(t)\ne 0$" is
--   formalized as: for a.e. $t \ge 0$ with $Z(t) \ne 0$, *every* real number that is a derivative
--   of $f$ at $t$ is at most $-\varepsilon$ (`∀ d, HasDerivAt f d t → d ≤ -ε`) — equivalent to
--   "$\dot f(t)$ exists and is $\le -\varepsilon$" whenever a derivative exists (which Lemma 8.3
--   guarantees almost everywhere), and vacuously true where it does not, avoiding a spurious
--   existence claim inside the hypothesis itself. $H(z) \ne 0$ for $z \ne 0$ is stated as strict
--   (not merely $H(z) \ge 0$), matching the book's positive-definiteness requirement exactly. The
--   capacity consumption matrix is nonnegative with no zero column (`hA`, `hAcol`, the standing
--   assumption on the SPN data of Section 2.1), which is what makes $Z$, hence $f$, Lipschitz
--   (Lemma 8.3) — the almost-everywhere drift bound has force only for an absolutely continuous
--   $f$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 136, Lemma 8.5

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_LipschitzOn
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData

namespace ProcessingNetworks.LyapunovCriteria

open MeasureTheory

/-- Lemma 8.5, Dai & Harrison p. 136 (PDF p. 152): let `H : ℝ^I_+ → ℝ_+` be Lipschitz with
`H(0) = 0` and `H(z) ≠ 0` for `z ≠ 0`. Consider a fluid model consisting of (6.1)-(6.6) plus
possibly other equations, and a solution `(D,F,T,Z)`; set `f(t) := H(Z(t))`. If there is `ε > 0`
such that `ḟ(t) ≤ -ε` for almost all `t` with `Z(t) ≠ 0` (8.2), then `Z(t) = 0` for
`t ≥ t₀ = f(0)/ε = H(Z(0))/ε`. -/
theorem lyapunov_extinction_linear
    {I : ℕ} (H : (Fin I → ℝ) → ℝ)
    (hH_lip : IsLipschitzOn H {z : Fin I → ℝ | ∀ i, 0 ≤ z i})
    (hH0 : H (fun _ => 0) = 0) (hHpos : ∀ z : Fin I → ℝ, z ≠ (fun _ => 0) → H z ≠ 0)
    {J K : ℕ} (dat : FluidEquationData I J K)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat Dh Fh Th Zh)
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → Zh t ≠ (fun _ => 0) →
      ∀ d : ℝ, HasDerivAt (fun s => H (Zh s)) d t → d ≤ -ε) :
    ∀ t : ℝ, H (Zh 0) / ε ≤ t → Zh t = fun _ => 0 := by sorry

end ProcessingNetworks.LyapunovCriteria
