-- Prove2me | Theorems.Thm_RelaxationMethod_FullDim_limit_mem_frontier
-- name    : RelaxationMethod.FullDim.limit_mem_frontier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:27:00.077846+00:00
-- url     : https://prove2.me/theorems/53bbae1f-54b8-46a5-b7ba-f57ec18b0ff5
-- title:
--   §5 — the limit of an infinite relaxation sequence lies on the boundary of $A$
-- statement:
--   Let $A$ be the nonempty solution polytope of a system of linear inequalities in $E_n$ and let $0 < \lambda \le 2$. Let $p_0, p_1, \dots$ be a run of the relaxation process with parameter $\lambda$ that never terminates ($p_\nu \notin A$ for all $\nu$). If
--
--   $$
--   \lim_{\nu\to\infty} p_\nu = l ,
--   $$
--
--   then $l$ belongs to the boundary of $A$: $l \in A$, and $l$ is not an interior point of $A$.
--
--   Together with Lemma 1 this completes the proof of Theorem 1, Case 1, and it is the second step of the proof of Theorem 1, Case 2.
--
--   **Formalization Note** The paper proves this in §5 for $0 < \lambda < 2$ and uses the same argument in §6 for $\lambda = 2$; we state it for $0 < \lambda \le 2$. No dimension hypothesis is needed. "Boundary" is the topological frontier `frontier A`; since $A$ is closed this means $l \in A \setminus \operatorname{int} A$. The parameter $\lambda$ is named `lam`.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 399, §5, (2.10)–(2.11), and §6

import Mathlib
import Definitions.Def_RelaxationMethod_FullDim_RelaxStep
import Definitions.Def_RelaxationMethod_FullDim_FejerMonotone
open Filter Topology

namespace RelaxationMethod.FullDim

/-- §5, p. 399 (reused in §6): if an infinite run of the relaxation process with `0 < lam ≤ 2`
converges to `l`, then `l` lies on the boundary of the nonempty polytope `A`. -/
theorem limit_mem_frontier {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsRelaxRun a b lam p)
    (hinf : ∀ ν : ℕ, p ν ∉ polytope a b) (l : EuclideanSpace ℝ (Fin n))
    (hl : Tendsto p atTop (𝓝 l)) :
    l ∈ frontier (polytope a b) := by sorry

end RelaxationMethod.FullDim
