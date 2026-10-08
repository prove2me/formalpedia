-- Prove2me | Theorems.Thm_WassDRCCP_Improved_eq_3_dual_form
-- name    : WassDRCCP.Improved.eq_3_dual_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:18.539681+00:00
-- url     : https://prove2.me/theorems/725a5820-88ed-4bc2-913b-71ceeb533602
-- title:
--   (3), p. 645 (Chen–Kuhn–Wiesemann, Thm 3) — X_DR(S) = {x ∈ X : ∃ t ≥ 0, r ≥ 0, dist(ξ_i, S(x)) ≥ t − r_i, ϵt ≥ θ + (1/N)Σr_i}
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra, $\xi_1, \dots, \xi_N \in E$ a sample with $N \ge 1$, $\epsilon \in (0, 1)$ and $\theta > 0$. Let $\mathcal X \subseteq \mathbb R^L$ and let $\mathcal S$ assign to each $x$ a set $\mathcal S(x) \subseteq E$ that, for every $x \in \mathcal X$, is open and has nonempty complement. Then
--   $$\mathcal X_{\mathrm{DR}}(\mathcal S) = \Big\{x \in \mathcal X : \exists\, t \ge 0,\ r \ge 0,\ \operatorname{dist}(\xi_i, \mathcal S(x)) \ge t - r_i\ (i \in [N]),\ \epsilon t \ge \theta + \tfrac1N \textstyle\sum_{i \in [N]} r_i\Big\},$$
--   where $\mathcal X_{\mathrm{DR}}(\mathcal S)$ is the set of $x \in \mathcal X$ whose worst-case violation probability $\sup_{\mathbb P \in \mathcal F_N(\theta)} \mathbb P[\xi \notin \mathcal S(x)]$ over the 1-Wasserstein ball of radius $\theta$ around the empirical distribution is at most $\epsilon$.
--
--   This is the result of Chen, Kuhn and Wiesemann (Theorem 3; also Xie, Proposition 1) that the paper cites and on which every one of its exact reformulations rests: it replaces a supremum over probability measures by finitely many scalar constraints. It is related to the strong duality for worst-case probabilities of Blanchet and Murthy, which is on the platform as `ModelRiskOT.WorstProb.eq_13`.
--
--   **Formalization Note** The worst-case probability is the published `worstProb` with cost $\|u - v\|$ around the published empirical distribution. The hypothesis that $E \setminus \mathcal S(x)$ is nonempty guards against Mathlib's junk value $\operatorname{dist}(\cdot, \emptyset) = 0$ (the paper's infimum would be $+\infty$); without it the right-hand side would wrongly exclude such $x$. $N \ge 1$, $\epsilon \in (0,1)$ and $\theta > 0$ are the paper's standing assumptions of §§2–4 (p. 645). Compactness of $\mathcal X$ is not assumed.
-- source:
--   Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, Math. Program. 196 (2022) 641–672, p. 645, (3), citing Chen, Kuhn & Wiesemann [8, Theorem 3]

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

open MeasureTheory
open scoped ENNReal

namespace WassDRCCP.Improved

/-- Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee (2022), (3), p. 645 (Chen, Kuhn & Wiesemann,
Theorem 3): when `S(x)` is open for each `x ∈ X` and `θ > 0`,
`X_DR(S) = {x ∈ X : ∃ t ≥ 0, r ≥ 0, dist(ξ_i, S(x)) ≥ t − r_i (i ∈ [N]), ϵ t ≥ θ + (1/N) Σ_i r_i}`.
The unsafe set `S(x)ᶜ` is assumed nonempty, so that the distance is finite. -/
theorem eq_3_dual_form
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {L N : ℕ}
    (S : (Fin L → ℝ) → Set E) (X : Set (Fin L → ℝ)) (ξ : Fin N → E) (ϵ θ : ℝ)
    (hN : 0 < N) (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) (hθ : 0 < θ)
    (hS_open : ∀ x ∈ X, IsOpen (S x)) (hS_compl : ∀ x ∈ X, (S x)ᶜ.Nonempty) :
    XDR S X ξ ϵ θ = dualSet S X ξ ϵ θ := by sorry

end WassDRCCP.Improved
