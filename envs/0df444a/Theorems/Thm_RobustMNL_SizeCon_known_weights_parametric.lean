-- Prove2me | Theorems.Thm_RobustMNL_SizeCon_known_weights_parametric
-- name    : RobustMNL.SizeCon.known_weights_parametric
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:44.356634+00:00
-- url     : https://prove2.me/theorems/1eb1f0cd-6266-4571-972b-9394f8a09551
-- title:
--   Proof of Theorem 3.8, p. 12 — max_{|S|≤K} f(S, (u₀, l)) = max{λ : max_{|S|≤K} (1/u₀) Σ l_i (r_i − λ) ≥ λ}
-- statement:
--   Let $u_0>0$ and $l_1,\dots,l_n>0$, let $r_1,\dots,r_n$ be real revenues and $K\in\mathbb N$. Write $h=(u_0,l_1,\dots,l_n)$ and $f(S,h)=\sum_{i\in S} l_i r_i/(u_0+\sum_{i\in S} l_i)$ for the MNL revenue of $S$ under the known weights $h$. Then
--
--   $$
--   \max_{S\subseteq\mathcal A:\ |S|\le K} f(S,h)
--   \;=\;\max\Big\{\lambda:\ \max_{S:\ |S|\le K}\ \frac{1}{u_0}\sum_{i\in S} l_i\,(r_i-\lambda)\ \ge\ \lambda\Big\}.
--   $$
--
--   This is the closing chain of the proof of Theorem 3.8: the parametric description of a size-constrained assortment problem with known weights. Combined with the parametric form of $Y^*$ and the rectangular reduction, it identifies $Y^*$ of a box with the known-weights optimum.
--
--   **Formalization Note** The "max" of the set of admissible $\lambda$ is `IsGreatest`. Revenues are arbitrary reals. Products are 0-indexed (`Fin n`).
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, proof of Theorem 3.8, p. 12, last display chain

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_RobustMNL_SizeCon_Model

namespace RobustMNL.SizeCon

/-- Proof of Theorem 3.8, p. 12, last chain: for positive weights `(u₀, l₁, …, lₙ)`,
`max_{|S| ≤ K} f(S, (u₀, l))` is the largest `λ` with
`λ ≤ max_{|S| ≤ K} (1/u₀) ∑_{i ∈ S} l_i (r_i − λ)`. -/
theorem known_weights_parametric {n : ℕ} (u₀ : ℝ) (l : Fin n → ℝ) (hu₀ : 0 < u₀)
    (hl : ∀ i, 0 < l i) (r : Fin n → ℝ) (K : ℕ) :
    IsGreatest
      {lam : ℝ | lam ≤ (sizeFeasible n K).sup' (sizeFeasible_nonempty n K)
        (fun S => (1 / u₀) * ∑ i ∈ S, l i * (r i - lam))}
      (knownMax r K (u₀, l)) := by sorry

end RobustMNL.SizeCon
