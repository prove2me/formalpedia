-- Prove2me | Theorems.Thm_ProcessingNetworks_LyapunovCriteria_lipschitz_composition
-- name    : ProcessingNetworks.LyapunovCriteria.lipschitz_composition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:56:44.573245+00:00
-- url     : https://prove2.me/theorems/10adacf0-dbf9-4e2b-845b-c124a6e37cc9
-- title:
--   Lemma 8.2 — composition of Lipschitz functions (milestone)
-- statement:
--   **Lemma 8.2.** If $g : \mathbb{R}^m \to \mathbb{R}$ and $h : \mathbb{R}_+ \to \mathbb{R}^m$
--   are both Lipschitz, then $f(t) := g(h(t))$ is Lipschitz on $\mathbb{R}_+$.
--
--   This is the composition lemma behind Lemma 8.5's proof, where $H$ (Lipschitz) is composed
--   with $Z$ (Lipschitz, by Lemma 8.3) to show $f(t) = H(Z(t))$ is Lipschitz.
--
--   **Formalization note.** $g$'s domain is `Set.univ` (all of $\mathbb{R}^m$, matching
--   "$g:\mathbb{R}^m\to\mathbb{R}$" with no positivity restriction) while $h$ and the conclusion
--   use `Set.Ici 0` (matching "$h:\mathbb{R}_+\to\mathbb{R}^m$").
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 136, Lemma 8.2

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_LipschitzOn

namespace ProcessingNetworks.LyapunovCriteria

/-- Lemma 8.2, Dai & Harrison p. 136 (PDF p. 152): if `g : ℝ^m → ℝ` and `h : ℝ_+ → ℝ^m` are both
Lipschitz, then `f(t) := g(h(t))` is Lipschitz on `ℝ_+`. -/
theorem lipschitz_composition {m : ℕ} (g : (Fin m → ℝ) → ℝ) (h : ℝ → Fin m → ℝ)
    (hg : IsLipschitzOn g Set.univ) (hh : IsLipschitzOn h (Set.Ici 0)) :
    IsLipschitzOn (fun t => g (h t)) (Set.Ici (0 : ℝ)) := by sorry

end ProcessingNetworks.LyapunovCriteria
