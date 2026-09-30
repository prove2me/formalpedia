-- Prove2me | Theorems.Thm_RelaxationMethod_LowDim_limit_mem_frontier
-- name    : RelaxationMethod.LowDim.limit_mem_frontier
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:30:51.716532+00:00
-- url     : https://prove2.me/theorems/4c923678-e283-47d5-a1ef-75472d618c77
-- title:
--   §5 — the limit of a convergent infinite relaxation sequence is a boundary point of $A$
-- statement:
--   Let $A$ be the nonempty solution polytope of a system of linear inequalities, let $0 < \lambda \leqslant 2$, and let $\{p_\nu\}$ be an infinite relaxation sequence (every $p_\nu \notin A$, each obtained from the previous one by a relaxation step with parameter $\lambda$). If $p_\nu \to l$, then
--   $$l \in A \quad\text{and}\quad l \in \partial A.$$
--
--   The argument of §5 uses the function $d(x) = \max_i \operatorname{dist}(x, H_i)$ that vanishes exactly on $A$. It is invoked in the proof of Theorem 2, Case 1 (§7) and, for $\lambda = 2$, in §6 and §8.
--
--   **Formalization Note** The paper proves this in §5 for $r = n$ and $0 < \lambda < 2$; the argument uses neither assumption, and §7 ($r < n$) and §8 ($\lambda = 2$) reuse it, so it is stated without a dimension hypothesis and for $0 < \lambda \leqslant 2$. The boundary is the topological frontier.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, p. 399, §5, (2.10)–(2.11)

import Mathlib
import Definitions.Def_RelaxationMethod_LowDim_RelaxStep

open Filter Topology

namespace RelaxationMethod.LowDim

/-- §5, p. 399: if an infinite relaxation sequence with `0 < λ ⩽ 2` converges to `l`, then `l`
belongs to `A`, and lies on the boundary of `A`. -/
theorem limit_mem_frontier {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : ∀ ν, p ν ∉ polytope a b → IsRelaxStep a b lam (p ν) (p (ν + 1)))
    (hinf : ∀ ν, p ν ∉ polytope a b) (l : EuclideanSpace ℝ (Fin n))
    (hl : Tendsto p atTop (𝓝 l)) :
    l ∈ polytope a b ∧ l ∈ frontier (polytope a b) := by sorry

end RelaxationMethod.LowDim
