-- Prove2me | Theorems.Thm_RelaxationMethod_LowDim_theorem2
-- name    : RelaxationMethod.LowDim.theorem2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:32:22.607396+00:00
-- url     : https://prove2.me/theorems/136dd6c4-d6df-4d8b-b30a-54c8173c4320
-- title:
--   Theorem 2 — for $r < n$ relaxation converges into $A$, and reflexion ends on a sphere with axis $L_r$
-- statement:
--   Let $A = \bigcap_{i=1}^m H_i$ be the solution polytope of a consistent system of linear inequalities $\sum_j a_{ij}x_j + b_i \geqslant 0$ in $E_n$, assumed nonempty, and let $L_r$ be the affine span of $A$. Assume $r < n$, i.e. $L_r \neq E_n$. Consider any sequence $p_0, p_1, \dots$ obtained by the relaxation process of §1 with parameter $\lambda$: as long as $p_\nu \notin A$, the point $p_{\nu+1}$ is obtained from $p_\nu$ by a relaxation step through a half-space at maximal distance. The process *terminates* if some $p_N \in A$.
--
--   1. **Case 1** ($0 < \lambda < 2$). Either the process terminates, or $p_\nu \to l$ for a point $l \in A$.
--   2. **Case 2** ($\lambda = 2$, the reflexion method). Either the process terminates, or there are an index $\nu_0$ and a point $c \notin L_r$ such that
--   $$|p_\nu - a| = |c - a| \quad \text{for all } a \in L_r \text{ and all } \nu \geqslant \nu_0,$$
--   that is, all $p_\nu$ with $\nu \geqslant \nu_0$ lie on one spherical surface $S_{n-r-1}$ having $L_r$ as its axis.
--
--   Case 1 is Agmon's convergence theorem, reproved. Case 2 is the paper's own result for the reflexion method; with Theorem 1 (the case $r = n$, where reflexion always terminates) it describes the reflexion method completely, and Corollary 1 derives from it that the hyperplanes used eventually contain $L_r$.
--
--   **Formalization Note** Both cases are stated for every run, under every rule for choosing among maximizing half-spaces in (1.5). "A ⊂ L_r" holds automatically since $L_r$ is defined as the affine span of $A$. The sphere is a single sphere for all $\nu \geqslant \nu_0$, and $c \notin L_r$ excludes the degenerate one-point locus.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, p. 396, Theorem 2, Cases 1 and 2 (proofs pp. 399–402, §§7–8)

import Mathlib
import Definitions.Def_RelaxationMethod_LowDim_RelaxStep
import Definitions.Def_RelaxationMethod_LowDim_AxisSphere

open Filter Topology

namespace RelaxationMethod.LowDim

/-- Theorem 2, p. 396. Let `A` be the (nonempty) solution polytope and `L_r = affineSpan ℝ A`
with `r < n`. Case 1: for `0 < λ < 2` every relaxation sequence either terminates or converges to
a point of `A`. Case 2: for `λ = 2` every reflexion sequence either terminates or, from some
index `ν₀` on, lies on one spherical surface having `L_r` as its axis. -/
theorem theorem2 {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (hr : affineSpan ℝ (polytope a b) ≠ ⊤) :
    (∀ lam : ℝ, 0 < lam → lam < 2 → ∀ p : ℕ → EuclideanSpace ℝ (Fin n),
        (∀ ν, p ν ∉ polytope a b → IsRelaxStep a b lam (p ν) (p (ν + 1))) →
        (∃ N, p N ∈ polytope a b) ∨ ∃ l ∈ polytope a b, Tendsto p atTop (𝓝 l)) ∧
    (∀ p : ℕ → EuclideanSpace ℝ (Fin n),
        (∀ ν, p ν ∉ polytope a b → IsRelaxStep a b 2 (p ν) (p (ν + 1))) →
        (∃ N, p N ∈ polytope a b) ∨
          ∃ ν₀ : ℕ, ∃ c ∉ affineSpan ℝ (polytope a b),
            ∀ ν ≥ ν₀, p ν ∈ axisSphere (affineSpan ℝ (polytope a b)) c) := by sorry

end RelaxationMethod.LowDim
