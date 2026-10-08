-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_theorem_2_1
-- name    : UniformPrecSched.Makespan.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:12:41.435982+00:00
-- url     : https://prove2.me/theorems/0b07674b-be74-4b52-ac5d-dfbb64979ad6
-- title:
--   Theorem 2.1 — speed-based list scheduling gives C_max ≤ C + Σ_k D_k
-- statement:
--   Let $I$ be an instance of $Q|prec|C_{\max}$ with distinct speeds $\bar s_1 > \cdots > \bar s_K$, $m_k$ machines of speed $\bar s_k$, and let $k(j)$ be any job assignment. Write
--   $$D_k = \frac{1}{m_k}\sum_{j : k(j)=k}\frac{p_j}{\bar s_k}, \qquad C = \max_{\mathcal C\ \text{chain}} \sum_{j\in\mathcal C}\frac{p_j}{\bar s_{k(j)}}.$$
--   Then every schedule produced by the speed-based list scheduling algorithm for this assignment has length
--   $$C_{\max} \le C + \sum_{k=1}^K D_k.$$
--
--   This is the generalization of Graham's analysis of list scheduling to machines of different speeds, and the bound that every later guarantee of the paper instantiates.
--
--   **Formalization Note** "Produced by the speed-based list scheduling algorithm" is the predicate `IsSpeedListSchedule` of the model file: every job runs at its assigned speed, and no machine of a job's assigned speed idles while that job is available and unstarted.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 4, Theorem 2.1

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model

namespace UniformPrecSched.Makespan

/-- Theorem 2.1 (p. 4): for any job assignment `k`, every schedule produced by the speed-based
list scheduling algorithm has length `C_max ≤ C + Σ_{k=1}^K D_k`. -/
theorem theorem_2_1 {n m : ℕ} (I : Instance n m) (k : Assignment I) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) :
    σ.makespan ≤ chainBound I k + ∑ κ, classLoad I k κ := by sorry

end UniformPrecSched.Makespan
