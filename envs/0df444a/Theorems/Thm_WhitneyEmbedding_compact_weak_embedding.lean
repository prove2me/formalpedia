-- Prove2me | Theorems.Thm_WhitneyEmbedding_compact_weak_embedding
-- name    : WhitneyEmbedding.compact_weak_embedding
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T11:45:07.042144+00:00
-- url     : https://prove2.me/theorems/a6a8df31-a549-4e0a-8e3c-468cb9d769ca
-- title:
--   Compact Whitney embedding in dimension $2n+1$
-- statement:
--   Every compact Hausdorff, second-countable smooth real $n$-manifold without boundary admits a smooth embedding into $\mathbb R^{2n+1}$. More precisely, there is a smooth map $e:M\to\mathbb R^{2n+1}$ which is a homeomorphism onto a closed image and whose differential is injective at every point. The given topology and smooth atlas are preserved. The statement includes $n=0$, the empty manifold and disconnected manifolds.
--
--   This is the weak compact dimension bound used as input to the strong Whitney embedding step.
-- source:
--   MIT 18.965 (Tomasz Mrowka), Fall 2004, Lecture 14, Theorem 15.1 and Lemma 15.2, printed pp. 30-31, https://ocw.mit.edu/courses/18-965-geometry-of-manifolds-fall-2004/56a9ee64fec614c749e37517a603bde9_lecture14.pdf . Also Marco Gualtieri, Geometry and Topology I (2012), Theorem 3.50, printed p.35, https://www.math.toronto.edu/mgualt/courses/MAT425F-2013/docs/1300-2012-notes.pdf . The closed-image refinement follows from compactness; second countability is explicit, and the harmless n=0 case is included.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.compact_weak_embedding (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e ∧ IsClosedEmbedding e ∧
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x) := by sorry
