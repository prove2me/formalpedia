-- Prove2me | Theorems.Thm_PersonalizedRM_RevenueGap_c_lower_bound
-- name    : PersonalizedRM.RevenueGap.c_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:54.61959+00:00
-- url     : https://prove2.me/theorems/70bba559-39ab-44f4-ae3a-712aaee7b590
-- title:
--   p. ec4 — P_z(j; S, θ)·P_z(0; S, θ) ≥ c = e^{−R}/[1 + e^{−R} + (J − 1)e^R]² on the ℓ1 ball
-- statement:
--   Let $\theta$ be a feasible parameter, $\|\theta\|_1 \le R$, let $z \in \mathbb R^d$ with $\|z\|_\infty \le 1$, let $S \subseteq [J]$ be an assortment and let $p \in [0,1]^J$ be a price vector. Then every offered product $j \in S$ satisfies
--
--   $$\mathbb P_z(j; S, p, \theta)\, \mathbb P_z(0; S, p, \theta) \ \ge\ c = \frac{e^{-R}}{[1 + e^{-R} + (J-1)e^R]^2}.$$
--
--   Together with Lemma EC.1 this gives a lower bound on the curvature of $\ell_n$ that is uniform over the feasible set, which is how the strong convexity parameter $\eta = \nu\rho c/2$ of (6) arises.
--
--   **Formalization Note.** The page states the bound "for any $z_i$, $S_i$, and $\theta$"; it uses that $\theta$ is feasible and that the feature–price vector has entries in $[-1, 1]$, so that every utility satisfies $|V_j| \le R$. These conditions are made explicit. Prices are only required to lie in $[0,1]$, which contains the price box $[p_{\min}, 1]$.
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), p. ec4, 'For any z_i, S_i, and θ, it must be true that …' (definition of c)

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

namespace PersonalizedRM.RevenueGap

/-- p. ec4: for a feasible parameter (`‖θ‖₁ ≤ R`), a bounded feature vector and prices in
`[0, 1]`, every offered product `j` has `P_z(j; S, θ) P_z(0; S, θ) ≥ c`. -/
theorem c_lower_bound {J d : ℕ} (R : ℝ) (θ : Param J d) (hθ : l1norm θ ≤ R)
    (z : Fin d → ℝ) (hz : ∀ k, |z k| ≤ 1) (S : Finset (Fin J)) (p : Fin J → ℝ)
    (hp : p ∈ priceBox J 0) (j : Fin J) (hj : j ∈ S) :
    cMin J R ≤ choiceProb θ z S p (some j) * choiceProb θ z S p none := by sorry

end PersonalizedRM.RevenueGap
