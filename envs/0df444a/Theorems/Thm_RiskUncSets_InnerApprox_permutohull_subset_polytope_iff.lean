-- Prove2me | Theorems.Thm_RiskUncSets_InnerApprox_permutohull_subset_polytope_iff
-- name    : RiskUncSets.InnerApprox.permutohull_subset_polytope_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:06:58.214622+00:00
-- url     : https://prove2.me/theorems/3814a51d-7cdd-4b43-b7fe-f201c62ddd15
-- title:
--   Proof of Theorem 4.5, p. 1493 — Π_q(𝒜) ⊆ 𝒰 iff there exist s₁, …, s_m, t₁, …, t_m with e′(s_k + t_k) ≥ v_k and s_{k,i} + t_{k,j} ≤ (u′_k a_j)q_i
-- statement:
--   Let $\mathcal A = \{a_1,\dots,a_N\} \subset \mathbb R^n$, let $q \in \mathbb R^N$ be any vector, and let
--   $\mathcal U = \{a \in \mathbb R^n : u_k' a \ge v_k,\ k = 1,\dots,m\}$ be the polyhedron (14). Then $\Pi_q(\mathcal A) \subseteq \mathcal U$ if and only if there exist $s_1,\dots,s_m, t_1,\dots,t_m \in \mathbb R^N$ such that
--   $$e'(s_k + t_k) \ge v_k\quad \forall k \in \{1,\dots,m\},\qquad s_{k,i} + t_{k,j} \le (u_k' a_j)\, q_i\quad \forall (i,j) \in \{1,\dots,N\}^2,\ \forall k \in \{1,\dots,m\}.$$
--
--   Containment of the permutohull in each half-space is a minimization over doubly stochastic matrices, and the displayed system is its dual (an assignment problem and its dual). This turns the containment constraint of Theorem 4.5 into the linear constraints of (15).
--
--   **Formalization Note** The vector $q$ is arbitrary in $\mathbb R^N$, with no sign or ordering condition: the linear program (15) applies this equivalence at $q = \lambda\hat q + (1-\lambda) e_N$, which may have negative entries. Indices are $0$-based in Lean. For $m = 0$ both sides hold trivially.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1493, proof of Theorem 4.5

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Proof of Theorem 4.5: `Π_q(𝒜) ⊆ 𝒰` iff there are `s_k, t_k ∈ ℝᴺ` with
`e′(s_k + t_k) ≥ v_k` and `s_{k,i} + t_{k,j} ≤ (u_k′ a_j) q_i`; for every `q ∈ ℝᴺ`. -/
theorem permutohull_subset_polytope_iff {N n m : ℕ} (q : Fin N → ℝ)
    (a : Fin N → Fin n → ℝ) (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) :
    permutohull q a ⊆ polytope u v ↔
      ∃ s t : Fin m → Fin N → ℝ, (∀ k, v k ≤ ∑ i, (s k i + t k i)) ∧
        ∀ k i j, s k i + t k j ≤ (u k ⬝ᵥ a j) * q i := by sorry

end RiskUncSets.InnerApprox
