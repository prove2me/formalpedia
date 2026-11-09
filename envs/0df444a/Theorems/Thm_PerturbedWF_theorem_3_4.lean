-- Prove2me | Theorems.Thm_PerturbedWF_theorem_3_4
-- name    : PerturbedWF.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:29:27.357369+00:00
-- url     : https://prove2.me/theorems/3987eca3-fca4-43e2-acc9-a0a0dfa96d5c
-- title:
--   Theorem 3.4: $\tau$-HSTs ($\tau>2$) have vectors $A_i$, $z_i$ in dimension $O(\log n+D)$ with $\|A_i-A_j\|_1\le d(i,j)$ and $\langle z_i,A_i-A_j\rangle\ge\frac{\tau-2}{16\tau}d(i,j)$
-- statement:
--   Let $([n],d)$ be the metric space of a $\tau$-HST of depth $D\ge1$ with $\tau>2$: the points are the leaves of a rooted tree with edge weights $w_e>0$ satisfying $w_f\le w_e/\tau$ for consecutive edges $e$ (upper) and $f$ (lower) on every root-to-leaf path, and $d$ is the weighted path length. For every leaf $i$ there are vectors $A_i\in\mathbb R^m$ and $z_i\in[-1,1]^m$ such that for all leaves $i,j$:
--   1. $\|A_i-A_j\|_1\le d(i,j)$;
--   2. $\langle z_i,A_i-A_j\rangle\ge c_\tau\,d(i,j)$,
--
--   where $m=O(\log n+D)$ and $c_\tau=(\tau-2)/(16\tau)$.
--
--   This low-dimensional representation is what replaces the dimension $n$ by $O(\log n+D)$ in the competitive ratio.
--
--   **Formalization Note.** The tree is a `PolylogKServer.HST.WTree` with `IsWeightedHST τ` (an edge is identified with its lower node); $n$ is the number of leaves and $D$ the height. "$m=O(\log n+D)$" is an absolute constant $K>0$, quantified before $\tau$ and the tree, with $m\le K(\log n+D)$ (natural logarithm).
--
--   Differences from the source:
--   - encoding: m = O(log n + D) → ∃ K > 0, quantified before τ and the tree, with m ≤ K(log n + D); reason: the O(·) is uniform over all HSTs and all τ; Appendix A gives m = 1 + 145L with L ≤ 2(log₂ n + D)
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Theorem 3.4, p.10 (PDF p.11); general proof Appendix A.2, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree

namespace PerturbedWF

/-- **Theorem 3.4** (p.10, PDF p.11). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

Let `([n], d)` be the metric space of a `τ`-HST of depth `D ≥ 1` with `τ > 2`. For every leaf
`i ∈ [n]` there exist vectors `A_i ∈ ℝ^m` and `z_i ∈ [−1, 1]^m` such that for every `i, j ∈ [n]`:
1. `‖A_i − A_j‖₁ ≤ d(i, j)`;
2. `⟨z_i, A_i − A_j⟩ ≥ c_τ d(i, j)`,

where `m = O(log n + D)` and `c_τ = (τ − 2)/(16τ)`.

**Formalization Note.** The `τ`-HST is a `PolylogKServer.HST.WTree` with `IsWeightedHST τ`
(`w_f ≤ w_e/τ` for consecutive edges, an edge identified with its lower node); its points are
the leaves, `d` is `treeDist`, `n = |T.Leaf|`, `D = T.height`. "`m = O(log n + D)`" is an
absolute constant `K > 0`, quantified before `τ` and the tree, with `m ≤ K (log n + D)`
(natural logarithm). -/
theorem theorem_3_4 :
    ∃ K : ℝ, 0 < K ∧ ∀ τ : ℝ, 2 < τ →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (T : PolylogKServer.HST.WTree V),
      T.IsWeightedHST τ → 1 ≤ T.height →
      ∃ m : ℕ, (m : ℝ) ≤ K * (Real.log (Fintype.card T.Leaf) + T.height) ∧
      ∃ A z : T.Leaf → Fin m → ℝ, (∀ i k, |z i k| ≤ 1) ∧
        ∀ i j, ∑ k, |A i k - A j k| ≤ T.treeDist i.1 j.1 ∧
          (τ - 2) / (16 * τ) * T.treeDist i.1 j.1 ≤ ∑ k, z i k * (A i k - A j k) := by sorry

end PerturbedWF
