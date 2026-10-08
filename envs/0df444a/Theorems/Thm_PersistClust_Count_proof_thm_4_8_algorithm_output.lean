-- Prove2me | Theorems.Thm_PersistClust_Count_proof_thm_4_8_algorithm_output
-- name    : PersistClust.Count.proof_thm_4_8_algorithm_output
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:29.495923+00:00
-- url     : https://prove2.me/theorems/4893df44-31c8-4c48-8cc4-4f714d314263
-- title:
--   Proof of Theorem 4.8, p. 23, with §3 p. 12 — the algorithm outputs one cluster per point of D₀𝓡 with prominence ≥ τ and birth ≥ τ
-- statement:
--   Let $g\in\mathbb R^n$, let $D$ be a symmetric $n\times n$ matrix with non-negative entries, let $\delta\ge0$ and $\tau>0$, and let $\sigma$ be any permutation sorting $g$ in non-decreasing order. Then the number of clusters output by the clustering algorithm (Procedures 1–2) with processing order $\sigma$ equals the number of points $q$ of the $0$-th persistence diagram $D_0\mathcal R^g_\delta$ of the upper-star Rips filtration, counted with multiplicity, such that
--   $$q_x-q_y\ge\tau\quad\text{and}\quad q_x\ge\tau,$$
--   the essential points $(q_x,-\infty)$ included.
--
--   This is the step "the algorithm discards $D^{\mathcal R}_1$ and keeps only $D^{\mathcal R}_2$" of the main theorem: the union-find procedure with the prominence test $g_{r(e)}-g_i<\tau$ and the output filter $g_{r(e)}\ge\tau$ selects exactly the points of the diagram above both thresholds, whatever the tie-breaking of the sort.
--
--   **Formalization Note** The hypothesis $\tau>0$ is added: with $\tau=0$ the algorithm may keep equal-valued adjacent peaks whose diagram point has zero persistence and is not counted. The main theorem has $\tau>d_1+2c\delta>0$. The paper asserts this step without proof.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), p. 23, proof of Theorem 4.8 ("the algorithm discards D^𝓡_1 and keeps only D^𝓡_2"), with p. 12, §3 (step 2 and the standard persistence algorithm)

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

namespace PersistClust.Count

theorem proof_thm_4_8_algorithm_output
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    (numClusters g Dm δ τ σ : ℕ∞)
      = {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < ripsDiagram Dm g δ q.1 ∧
          q.1.2 ≤ q.1.1 - (τ : EReal) ∧ (τ : EReal) ≤ q.1.1}.encard := by sorry

end PersistClust.Count
