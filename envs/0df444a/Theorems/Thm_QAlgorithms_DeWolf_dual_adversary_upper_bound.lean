-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_dual_adversary_upper_bound
-- name    : QAlgorithms.DeWolf.dual_adversary_upper_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:43:38.800973+00:00
-- url     : https://prove2.me/theorems/48dfe3ce-b8a1-4077-ae14-6128deac5dcf
-- title:
--   A dual-adversary solution of value A gives an O(A)-query bounded-error algorithm
-- statement:
--   There is an absolute constant $C > 0$ with the following property.
--
--   Let $N \ge 1$, let $f : D \to \{0,1\}$ with $D \subseteq \{0,1\}^N$, and let $\{u_{xj}, v_{xj}\}_{x \in D, j \in [N]}$ be vectors in $\mathbb C^d$ (for some $d$) forming a feasible solution of the dual SDP for $\mathrm{ADV}^{\pm}(f)$:
--
--   $$
--   \sum_{j : x_j \ne y_j} \langle u_{xj} | v_{yj} \rangle = [f(x) \ne f(y)] \quad \text{for all } x, y \in D.
--   $$
--
--   Suppose its objective value $\max_{x \in D} \max\left(\sum_j \|u_{xj}\|^2, \sum_j \|v_{xj}\|^2\right)$ is at most $A$, where $A \ge 1$. Then there is a $T$-query quantum algorithm $U_T O_x \cdots O_x U_0$ (input-independent unitaries on the query register and an $m$-qubit-indexed workspace, standard query $O_x : |i,b\rangle \mapsto |i,b\oplus x_i\rangle$, followed by a computational-basis measurement and a fixed output rule) with
--
--   $$
--   T \le C \cdot A
--   $$
--
--   that outputs $f(x)$ with probability at least $2/3$ for every $x \in D$.
--
--   Together with the generalized adversary lower bound, this shows that $\mathrm{ADV}^{\pm}(f)$ characterizes bounded-error quantum query complexity up to a constant factor. Only queries are counted, not gates.
--
--   **Formalization Note** The source's "small error probability" is pinned to the notes' bounded-error convention (error at most $1/3$); its "we may assume $A \ge 1$" is the hypothesis $1 \le A$. The workspace is `Fin m` for some $m$. The hypothesis $N \ge 1$ is the standing convention that inputs have at least one bit: with $N = 0$ the frozen model has no query register and admits no algorithm at all.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 114, §12.3, unnumbered. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Adversary
set_option autoImplicit false

namespace QAlgorithms.DeWolf




/-- de Wolf §12.3 (PDF pp. 114–116), the generalized adversary bound upper-bounds quantum query
complexity: there is an absolute constant `C > 0` such that for every `N ≥ 1`, every
`f : D → {0,1}` with `D ⊆ {0,1}^N`, and every feasible solution `{u_xj, v_xj}` (of any dimension
`d`) of the dual SDP for `ADV±(f)` with objective value at most `A`, where `A ≥ 1`, there is a
query algorithm with at most `C · A` queries that computes `f` with error probability at most
`1/3` on every `x ∈ D`. "Small error probability" is the notes' bounded-error convention; the
assumption `A ≥ 1` is the source's "we may assume A ≥ 1" (p. 116). -/
theorem dual_adversary_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (D : Finset (Fin N → Bool))
      (f : (Fin N → Bool) → Bool) (d : ℕ) (u v : D → Fin N → EuclideanSpace ℂ (Fin d)) (A : ℝ),
      DualFeasibleDeWolf f D d u v → (dewolfDualObjective u v : ℝ) ≤ A → 1 ≤ A →
        ∃ (m T : ℕ) (alg : QueryAlg (Fin N) Bool (Fin m) T)
          (out : (Fin N × Bool) × Fin m → Bool),
          (T : ℝ) ≤ C * A ∧ alg.ComputesWithError out D f (1 / 3) := by
  sorry



end QAlgorithms.DeWolf
