-- Prove2me | Theorems.Thm_PolyaLaplacian_polya_disk
-- name    : PolyaLaplacian.polya_disk
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T13:52:01.045604+00:00
-- url     : https://prove2.me/theorems/f2bdd762-b432-4e66-9e81-9bdbdb3050ea
-- title:
--   Pólya for the disk (FLPS 2023, Thm 1.2)
-- statement:
--   Pólya's conjecture for the **disk** (Filonov–Levitin–Polterovich–Sher 2023, Theorem 1.2, planar Dirichlet case).
--
--   For every radius $R>0$ and every $k\ge1$, the $k$-th Dirichlet eigenvalue of the disk $D_R=\{x:\|x\|<R\}$ satisfies
--   $$\lambda_k(D_R)\ \ge\ \frac{4\pi k}{|D_R|}\;=\;\frac{4k}{R^2}.$$
--   This was the first non-tiling planar domain for which the conjecture was verified. The paper proves the Dirichlet case for balls in all dimensions $d\ge2$; this milestone is the planar instance. It rules out disks as counterexamples.
--
--   **Formalization Note.** The disk is `disk R` and the bound is written in the uniform Pólya form $4\pi k/\text{area}$; the equality with $4k/R^2$ uses $|D_R|=\pi R^2$.
-- source:
--   Filonov–Levitin–Polterovich–Sher, Pólya's conjecture for Euclidean balls, Invent. Math. 234 (2023), 129–169, Theorem 1.2 (planar Dirichlet case), https://arxiv.org/abs/2203.07696

import Mathlib
import Definitions.Def_PolyaLaplacian_Spectral
open MeasureTheory Set TopologicalSpace

namespace PolyaLaplacian

theorem polya_disk (R : ℝ) (hR : 0 < R) (k : ℕ) (hk : 1 ≤ k) :
    dirichletEigenvalue (disk R : Set (EuclideanSpace ℝ (Fin 2))) k ≥
      4 * Real.pi * (k : ℝ) / area (disk R : Set (EuclideanSpace ℝ (Fin 2))) := by sorry

end PolyaLaplacian
