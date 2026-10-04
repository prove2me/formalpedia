-- Prove2me | Theorems.Thm_TeschlODE_HigherDim_unstableSet_subset_omegaPlusSet
-- name    : TeschlODE.HigherDim.unstableSet_subset_omegaPlusSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T16:43:23.897722+00:00
-- url     : https://prove2.me/theorems/bc163830-4a72-4c7d-9236-8555a2fc4a75
-- title:
--   Lemma 8.6 — $W^-(x) \subseteq \omega_+(E)$ for every $x \in \omega_+(E)$ (8.11)
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, $\Phi$ the flow of $\dot x = f(x)$ on $M$, and $E$ a trapping region. Then
--   $$W^-(x) \subseteq \omega_+(E) \qquad \text{for all } x \in \omega_+(E), \qquad (8.11)$$
--   where $W^-(x) = W^-(\{x\})$ is the set of points whose solution exists for all negative times and tends to $x$ as $t \to -\infty$.
--
--   In words: an attracting set obtained from a trapping region contains the unstable manifolds of all its points — which is why it can contain repelling fixed points (the example (8.3)).
--
--   **Formalization Note.** Standing assumptions as for Lemma 8.5. $W^-(x)$ is the unstable set (8.8) of the singleton $\{x\}$, i.e. `stableSet M I Φ (-1) {x}`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 232, Lemma 8.6, Eq. (8.11)

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_omegaPlusSet
import Definitions.Def_TeschlODE_HigherDim_stableSet
import Definitions.Def_TeschlODE_HigherDim_IsTrappingRegion

namespace TeschlODE.HigherDim

/-- Teschl, Lemma 8.6, p. 232, (8.11): for a trapping region `E`, the unstable set
`W⁻(x) = W⁻({x})` of every point `x ∈ ω₊(E)` is contained in `ω₊(E)`. -/
theorem unstableSet_subset_omegaPlusSet {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsTrappingRegion M I Φ E) :
    ∀ x ∈ omegaPlusSet M I Φ E, stableSet M I Φ (-1) {x} ⊆ omegaPlusSet M I Φ E := by sorry

end TeschlODE.HigherDim
