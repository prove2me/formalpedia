-- Prove2me | Theorems.Thm_TeschlODE_HigherDim_trapping_region_attracting
-- name    : TeschlODE.HigherDim.trapping_region_attracting
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T16:38:32.405013+00:00
-- url     : https://prove2.me/theorems/a28910e6-9774-4c6c-a046-ff87cb87875c
-- title:
--   Lemma 8.5 — a trapping region yields a nonempty, invariant, compact, connected attracting set $\omega_+(E)$
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, and $\Phi$ the flow of $\dot x = f(x)$ on $M$. Let $E$ be a trapping region. Then
--   $$\Lambda = \omega_+(E) = \bigcap_{t \ge 0} \Phi(t, E) \qquad (8.10)$$
--   is a nonempty, invariant, compact, and connected attracting set.
--
--   Lemma 8.5 is how attracting sets are found in practice: exhibit a region into which the vector field points (for the Lorenz equation, a sublevel set of a Liapunov-type function), and $\omega_+(E)$ is the attractor.
--
--   **Formalization Note.** The standing assumptions of Chapter 6 ($M$ open, $f \in C^1$) are binders. The book assumes the flow complete in Chapter 8; the statement uses the local flow, which is more general: the trapping-region definition already makes every point of $\overline E$ forward complete. "Invariant" is the book's two-sided invariance (every orbit through $\Lambda$ stays in $\Lambda$); "attracting" is $W^+(\Lambda)$ being a neighborhood of $\Lambda$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 232, Lemma 8.5, Eq. (8.10)

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_omegaPlusSet
import Definitions.Def_TeschlODE_HigherDim_stableSet
import Definitions.Def_TeschlODE_HigherDim_IsInvariant
import Definitions.Def_TeschlODE_HigherDim_IsAttracting
import Definitions.Def_TeschlODE_HigherDim_IsTrappingRegion

namespace TeschlODE.HigherDim

/-- Teschl, Lemma 8.5, p. 232, (8.10): for a trapping region `E` of the flow of a `C¹` vector
field on the open set `M ⊆ ℝⁿ`, `Λ = ω₊(E) = ⋂_{t ≥ 0} Φ(t, E)` is a nonempty, invariant,
compact, and connected attracting set. -/
theorem trapping_region_attracting {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsTrappingRegion M I Φ E) :
    omegaPlusSet M I Φ E = (⋂ t : ℝ, ⋂ (_ : 0 ≤ t), Φ t '' E) ∧
      (omegaPlusSet M I Φ E).Nonempty ∧ IsInvariant M I Φ (omegaPlusSet M I Φ E) ∧
      IsCompact (omegaPlusSet M I Φ E) ∧ IsConnected (omegaPlusSet M I Φ E) ∧
      IsAttracting M I Φ (omegaPlusSet M I Φ E) := by sorry

end TeschlODE.HigherDim
