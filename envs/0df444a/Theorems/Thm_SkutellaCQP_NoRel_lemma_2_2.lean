-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_lemma_2_2
-- name    : SkutellaCQP.NoRel.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:00.779046+00:00
-- url     : https://prove2.me/theorems/2d4abf1c-386b-4b49-8cb1-a52c1aa525e9
-- title:
--   Lemma 2.2, p. 8 — for any random assignment, E[Cⱼ] = Σᵢ (Pr[j ↦ i]·pᵢⱼ + Σ_{k ≺ᵢ j} Pr[j,k ↦ i]·pᵢₖ)
-- statement:
--   Consider an algorithm that assigns each job randomly to one of the $m$ machines, i.e. a probability distribution $\mu$ on assignments $\sigma$ (no independence between jobs is assumed), and let every machine sequence its jobs by Smith's order $\prec_i$. Write $\Pr[j\mapsto i]$ for the probability that job $j$ is assigned to machine $i$ and $\Pr[j,k\mapsto i]$ for the probability that both $j$ and $k$ are. Then for every job $j$
--
--   $$
--   \mathbb E[C_j]=\sum_{i=1}^m\Bigl(\Pr[j\mapsto i]\cdot p_{ij}+\sum_{k\prec_i j}\Pr[j,k\mapsto i]\cdot p_{ik}\Bigr).
--   $$
--
--   This expresses the expected completion time through the one- and two-job marginals of the random assignment only; it is the step from which the expected value of randomized rounding (Theorem 2.1) is computed.
--
--   **Formalization Note** The distribution is a nonnegative weight $\mu$ on the finite set of assignments with total mass $1$, and $\mathbb E[C_j]=\sum_\sigma\mu(\sigma)C_j(\sigma)$. The standing assumptions $p_{ij}>0$, $w_j\ge 0$ are carried as hypotheses.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 8, Lemma 2.2

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

open Finset

/-- Lemma 2.2 (p. 8). For any random assignment of jobs to machines (a probability weight `μ` on
assignments, with no independence assumed), the expected completion time of job `j` under Smith
sequencing is `∑_i (Pr[j ↦ i] p_ij + ∑_{k ≺_i j} Pr[j, k ↦ i] p_ik)`. -/
theorem lemma_2_2 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (μ : (Fin n → Fin m) → ℝ) (hμ0 : ∀ σ, 0 ≤ μ σ) (hμ1 : ∑ σ, μ σ = 1) (j : Fin n) :
    E μ (fun σ => compl p w σ j) =
      ∑ i, ((∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i), μ σ) * p i j +
        ∑ k ∈ univ.filter (fun k => prec p w i k j),
          (∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i ∧ σ k = i), μ σ) * p i k) := by sorry

end SkutellaCQP.NoRel
