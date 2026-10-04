-- Prove2me | Theorems.Thm_PolylogKServer_HST_exists_shallow_weighted_hst
-- name    : PolylogKServer.HST.exists_shallow_weighted_hst
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:49:13.992246+00:00
-- url     : https://prove2.me/theorems/f43509a3-4cb5-4a7e-9baa-8be876d2c24e
-- title:
--   Theorem 8 — every σ-HST becomes a weighted σ-HST of depth O(log n) with distortion ≤ 2σ/(σ−1)
-- statement:
--   There is a universal constant $C>0$ such that the following holds for every $\sigma>1$. Let $T$ be a $\sigma$-HST with $n\ge2$ leaves, of arbitrary depth. Then there is a weighted $\sigma$-HST $\tilde T$ whose leaves are identified with those of $T$ by a bijection $e$, such that $\tilde T$ has depth at most $C\log n$ and for all leaves $u,v$ of $T$
--   $$
--   d_{\tilde T}(e(u),e(v))\ \le\ d_T(u,v)\ \le\ \frac{2\sigma}{\sigma-1}\,d_{\tilde T}(e(u),e(v)).
--   $$
--
--   It lets the paper apply Theorem 6, whose ratio depends on the depth, to the HSTs of the Fakcharoenphol–Rao–Talwar embedding, whose depth depends on the aspect ratio of the metric.
--
--   **Formalization Note** "Distorted by a factor of at most $2\sigma/(\sigma-1)$" is stated as the two inequalities above: the new tree does not lengthen distances and shortens them by at most that factor. The $O(\log n)$ is a universal constant quantified before $\sigma$ and $T$. The guards $\sigma>1$ and $n\ge2$ are added: $2\sigma/(\sigma-1)$ needs $\sigma>1$, and with one leaf $\log n=0$.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 9, Theorem 8 (restated p. 35)

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree

namespace PolylogKServer.HST

/-- **Theorem 8** (arXiv:1110.1580v1, p. 9, restated p. 35). There is a universal constant
`C > 0` such that for every `σ > 1` and every σ-HST `T` with `n ≥ 2` leaves (of arbitrary
depth) there is a weighted σ-HST `T'` whose leaves are identified with those of `T` by a
bijection `e`, whose depth is at most `C · log n`, and in which every leaf-to-leaf distance of
`T` is distorted by a factor of at most `2σ/(σ − 1)`:
`d_{T'}(e u, e v) ≤ d_T(u, v) ≤ (2σ/(σ − 1)) · d_{T'}(e u, e v)`. -/
theorem exists_shallow_weighted_hst :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 1 < σ →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
        2 ≤ Fintype.card T.Leaf →
        ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (T' : WTree V')
          (e : T.Leaf ≃ T'.Leaf),
          T'.IsWeightedHST σ ∧
          (T'.height : ℝ) ≤ C * Real.log (Fintype.card T.Leaf) ∧
          ∀ u v : T.Leaf,
            T'.treeDist (e u) (e v) ≤ T.treeDist u v ∧
            T.treeDist u v ≤ 2 * σ / (σ - 1) * T'.treeDist (e u) (e v) := by sorry

end PolylogKServer.HST
