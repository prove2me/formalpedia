-- Prove2me | Theorems.Thm_WassersteinDRO_ConvexLossP1_wasserstein_one_le_p_ball_subset
-- name    : WassersteinDRO.ConvexLossP1.wasserstein_one_le_p_ball_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:52:31.260969+00:00
-- url     : https://prove2.me/theorems/16564386-e74d-4e2a-9204-0113e70043d4
-- title:
--   $W_p \ge W_1$, so $\mathbb B_{\varepsilon,p} \subseteq \mathbb B_{\varepsilon,1}$
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, let $p \ge 1$, let $\mathbb P$ be a Borel probability measure on $E$, let $\Xi \subseteq E$ and $\varepsilon \in \mathbb R$. Then
--
--   1. $W_p(\mathbb Q, \mathbb P) \ge W_1(\mathbb Q, \mathbb P)$ for every Borel probability measure $\mathbb Q$ on $E$;
--   2. consequently
--   $$\mathbb B_{\varepsilon,p}(\mathbb P) \subseteq \mathbb B_{\varepsilon,1}(\mathbb P).$$
--
--   The inequality comes from the convexity of $t \mapsto t^p$ on $[0, \infty)$ (Jensen's inequality applied to each coupling). It reduces upper bounds on the type-$p$ worst-case risk to the type-$1$ case.
--
--   Differences from the source:
--   - generalization: centre the nominal distribution P̂N → any Borel probability measure P; reason: the inequality holds for every centre and specializes to P = P̂N.
--   - generalization: ∀ Q ∈ P(Ξ) → every Borel probability measure Q on E; reason: P(Ξ) is a subset of all probability measures, so the paper's display is a special case.
--   - generalization: Ξ ⊆ R^m closed, radius ε ≥ 0 (p. 6) → any set Ξ ⊆ E and any real ε (a negative ε acts as radius 0 through ENNReal.ofReal); reason: the inclusion holds for every Ξ and ε, and specializes to closed Ξ and ε ≥ 0.
--   - encoding: R^m with an arbitrary norm → a finite-dimensional real normed space E; reason: same instances up to linear isometry.
--   - encoding: P(Ξ), distributions supported on Ξ → Borel probability measures Q with Q(Ξᶜ) = 0; reason: the standard meaning of "supported on Ξ" for a closed Ξ.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §2.1, unnumbered display, p. 9

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_ambiguityBall

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **`W_p ≥ W_1`, hence the type-`p` ball lies in the type-`1` ball.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §2.1, unnumbered display, p. 9: "the transportation cost ‖ξ − ξ′‖^p is a convex function of
the random variable ‖ξ − ξ′‖ for any p ≥ 1. Jensen's inequality thus implies
W_p(Q, P̂N) ≥ W_1(Q, P̂N) ∀Q ∈ P(Ξ) =⇒ B_{ε,p}(P̂N) ⊆ B_{ε,1}(P̂N)."

For every `p ≥ 1`, every Borel probability measure `P` on `E`, every `Ξ ⊆ E` and every `ε`:
`W_1(Q, P) ≤ W_p(Q, P)` for every Borel probability measure `Q`, and
`B_{ε,p}(P) ⊆ B_{ε,1}(P)`.

**Formalization Note.** The centre is any probability measure `P` rather than the nominal
distribution `P̂_N`, and the inequality is stated for every probability measure `Q` rather than
only for those supported on `Ξ`; both specialize to the paper's display. -/
theorem wasserstein_one_le_p_ball_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {p : ℝ} (hp : 1 ≤ p) (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (ε : ℝ) :
    (∀ Q : Measure E, IsProbabilityMeasure Q → wasserstein 1 Q P ≤ wasserstein p Q P) ∧
      ambiguityBall ε p P Ξ ⊆ ambiguityBall ε 1 P Ξ := by sorry

end WassersteinDRO.ConvexLossP1
