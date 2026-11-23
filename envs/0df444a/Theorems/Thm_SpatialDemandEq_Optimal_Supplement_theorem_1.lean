-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_Supplement_theorem_1
-- name    : SpatialDemandEq.Optimal.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:37:58.816606+00:00
-- url     : https://prove2.me/theorems/94484849-04ea-4322-b376-d79eaf84ba98
-- title:
--   Theorem 1, p. 9 — every fixed point w* ∈ 𝒲 of φ_k(w) = min{f_k(A_k(w)), w̄*} solves the equilibrium condition (3)
-- statement:
--   Work in the spatial service model: a closed convex region $\mathcal S \subseteq \mathbb R^n$ with normalized demand $\nu$ (a probability measure on $\mathcal S$, absolutely continuous), a continuous metric $d$, facilities $x_1,\dots,x_K \in \mathcal S$ with distances $d_k(x) = d(x,x_k)$ satisfying the regularity condition, and constants $c > 0$, $\lambda > 0$. Let the service rates satisfy $\mu_k > 0$ for every $k$ and $\sum_k \mu_k > \lambda$.
--
--   For weights $w \in \mathbb R^K$ let $A_k(w) = \nu(\mathcal A_k(w))$ be the area of the weighted Voronoi cell $\mathcal A_k(w) = \{x \in \mathcal S : d_k(x) + w_k \le d_j(x) + w_j\ \forall j \ne k\}$, and let $f_k(A) = c/(\mu_k - \lambda A)$ for $\lambda A < \mu_k$, $f_k(A) = +\infty$ otherwise. Let $\bar w$ be the optimal value of (4), and
--   $$\bar w^* = \max\Bigl\{1 + \bar w + \sup_{x \in \mathcal S, j, k}|d_j(x) - d_k(x)|,\ \max_k f_k(0)\Bigr\},\quad \mathcal W = \{w : 0 \le w_k \le \bar w^*\},\quad \phi_k(w) = \min\{f_k(A_k(w)), \bar w^*\}.$$
--
--   If $w^* \in \mathcal W$ is a fixed point, $w^* = \phi(w^*)$, then $w^*$ solves the equilibrium condition (3):
--   $$\lambda A_k(w^*) < \mu_k \quad\text{and}\quad w^*_k = f_k(A_k(w^*)) = \frac{c}{\mu_k - \lambda A_k(w^*)} \qquad \text{for every } k .$$
--
--   Together with the existence of a fixed point of $\phi$ (Lemma 3, by Brouwer's theorem), this yields the existence of equilibrium weights, and hence of the decentralized demand equilibrium.
--
--   **Formalization Note** The model's standing assumptions are the published `Standing` predicate of the base mission (including its disclosed conventions: each $d_k$ is $\nu$-integrable, and positive intensity is dropped). $\bar w^*$ is formed in the extended reals and converted to a real number; it is finite under the hypotheses by Lemma 2.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3.1 → the published `Standing S ν dst xs c lam` of the base mission; reason: inherited base conventions (ν-integrable d_k added, positive intensity λ(x) > 0 dropped), disclosed on the published definition
--   - encoding: w̄* is a real number once w̄ < ∞ → w̄* is the `EReal` maximum converted by `toReal`; reason: under the hypotheses μ_k > 0, λ < Σ μ_k (Lemma 2) and the metric bound |d_j − d_k| ≤ d(x_j, x_k) the maximum is finite, so the conversion is exact
--   - encoding: the equilibrium condition (3) w*_k = f_k(A_k(w*)) with f_k possibly ∞ → `IsEqWeight`: λA_k(w*) < μ_k and w*_k = c/(μ_k − λA_k(w*)); reason: a real w*_k equals f_k(A_k(w*)) exactly when f_k(A_k(w*)) is finite; same instances
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 9, Theorem 1 (with 𝒲, w̄*, φ defined on p. 9)

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_Model

open MeasureTheory SpatialDemandEq.Optimal

namespace SpatialDemandEq.Optimal.Supplement

theorem theorem_1 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (μ : Fin K → ℝ)
    (hμ : ∀ k, 0 < μ k) (hcap : lam < ∑ k, μ k) (w : Fin K → ℝ)
    (hW : w ∈ boxW S (distFn dst xs) c lam μ)
    (hfix : ∀ k, phi ν S (distFn dst xs) c lam μ w k = w k) :
    IsEqWeight ν S (distFn dst xs) c lam μ w := by sorry

end SpatialDemandEq.Optimal.Supplement
