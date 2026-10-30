-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_corollary8
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.corollary8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:39:53.675827+00:00
-- url     : https://prove2.me/theorems/10f0b17a-4b27-4a57-b6ac-cb8b3895ab87
-- title:
--   Corollary 8: full spectrum, multiplicities and top eigenvector
-- statement:
--   Let $N\ge1$. The full teleportation matrix $M_N$ is indexed by all $N$-box Young diagrams, with removable-corner counts on the diagonal and one on distinct single-box-move pairs. For $d\ge1$, $M_N^{(d)}$ is its principal restriction to shapes of height at most $d$, retaining the same diagonal counts.
--
--   The full matrix is positive semidefinite and
--
--   $$
--   \operatorname{spec}(M_N)=\{N\}\cup\{k\in\mathbb N:k+2\le N\},\qquad
--   \operatorname{mult}(k)=\#\{(\xi_2,\ldots,\xi_N)\in\mathbb N^{N-1}:k+\sum_{\ell=2}^N\ell\xi_\ell=N\}.
--   $$
--
--   Here multiplicity is algebraic multiplicity; the displayed count is also zero for natural numbers outside the spectrum. The dimension vector $v_\mu=d_\mu=\dim S^\mu$ is strictly positive and satisfies $M_Nv=Nv$. The largest eigenvalue and spectral radius are $N$, with multiplicity one. When their indices are nonnegative, $N-2$ and $N-3$ are simple and $N-4,N-5$ have multiplicity two. The displayed count specifies every further multiplicity. Physically this full spectrum applies when $d\ge N$.
--
--   These clauses describe the full spectrum, including its missing value $N-1$.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 10, Corollary 8: full spectrum, multiplicities and top eigenvector

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Corollary 8, all five clauses (PDF p.10). k+2<=N replaces the misleading
truncated range at N=1. Examples N-j have guards N>=j. The positive vector is
specifically the dimensions, not every scalar multiple of a top eigenvector. -/
theorem corollary8 {N : ℕ} (hN : 0 < N) :
    spectrum ℝ (fullMatrix N) = {r | ∃ k : ℕ, (k = N ∨ k+2 ≤ N) ∧ r = (k : ℝ)} ∧
    (fullMatrix N).PosSemidef ∧
    (∀ k : ℕ, (fullMatrix N).charpoly.roots.count (k : ℝ) = cycleClassCount N k) ∧
    (∀ mu : Partition N N, 0 < irrepDim mu) ∧
    (fullMatrix N) *ᵥ (fun mu => (irrepDim mu : ℝ)) =
      (N : ℝ) • (fun mu => (irrepDim mu : ℝ)) ∧
    topValue (fullMatrix N) = N ∧
    (fullMatrix N).charpoly.roots.count (N : ℝ) = 1 ∧
    (2 ≤ N → (fullMatrix N).charpoly.roots.count ((N : ℝ)-2) = 1) ∧
    (3 ≤ N → (fullMatrix N).charpoly.roots.count ((N : ℝ)-3) = 1) ∧
    (4 ≤ N → (fullMatrix N).charpoly.roots.count ((N : ℝ)-4) = 2) ∧
    (5 ≤ N → (fullMatrix N).charpoly.roots.count ((N : ℝ)-5) = 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
