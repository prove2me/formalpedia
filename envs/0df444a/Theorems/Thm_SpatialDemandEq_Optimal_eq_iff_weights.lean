-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_eq_iff_weights
-- name    : SpatialDemandEq.Optimal.eq_iff_weights
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:15.729053+00:00
-- url     : https://prove2.me/theorems/27595a6b-6846-4341-a67d-b1f6995a81a4
-- title:
--   p. 8 — the demand equilibria (1) are exactly the weighted Voronoi diagrams A_k(w*) with weights solving (3)
-- statement:
--   Assume the standing assumptions of the spatial model and service rates $\mu \in \mathbb R^K$ with $\sum_k \mu_k > \lambda$.
--
--   1. If $(\mathcal A_k)$ is a decentralized demand equilibrium (1) under $\mu$, then the weights $w_k = c/(\mu_k - \lambda A_k)$ solve the equilibrium condition
--   $$w_k = f_k(A_k(w)) = \frac{c}{\mu_k - \lambda A_k(w)}, \qquad \lambda A_k(w) < \mu_k, \tag{3}$$
--   and $\mathcal A_k = \mathcal A_k(w)$ up to a $\nu$-null set for every $k$.
--   2. Conversely, if $w$ solves (3), then the cells $(\mathcal A_k(w))_k$ form a decentralized demand equilibrium (1) under $\mu$.
--
--   In the paper's words, (1) describes a particular additively weighted Voronoi diagram whose weights are chosen to satisfy (3). This equivalence transfers uniqueness of the weights (Theorem 2) to uniqueness of the equilibrium partition.
--
--   **Formalization Note** The waiting cost is real-valued with the stability conjunct $\lambda A_k < \mu_k$ in both (1) and (3) (see the model file). The equality in part 1 is up to $\nu$-null sets, because an equilibrium partition may differ from the Voronoi cells on the null set of ties.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 8, equilibrium condition (3) and 'In other words, (1) describes a particular additively weighted Voronoi diagram whose weights are chosen to satisfy (3)'; (1), p. 7

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem eq_iff_weights {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (μ : Fin K → ℝ)
    (hcap : lam < ∑ k, μ k) :
    (∀ A : Fin K → Set (E n), IsDecentralizedEq ν S (distFn dst xs) c lam μ A →
        IsEqWeight ν S (distFn dst xs) c lam μ (fun i => c / (μ i - lam * area ν (A i))) ∧
          ∀ k, A k =ᵐ[ν] cell S (distFn dst xs) (fun i => c / (μ i - lam * area ν (A i))) k) ∧
      ∀ w : Fin K → ℝ, IsEqWeight ν S (distFn dst xs) c lam μ w →
        IsDecentralizedEq ν S (distFn dst xs) c lam μ (cell S (distFn dst xs) w) := by sorry

end SpatialDemandEq.Optimal
