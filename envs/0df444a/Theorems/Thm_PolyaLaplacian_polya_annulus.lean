-- Prove2me | Theorems.Thm_PolyaLaplacian_polya_annulus
-- name    : PolyaLaplacian.polya_annulus
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T13:52:29.940203+00:00
-- url     : https://prove2.me/theorems/1158a7cd-1778-4703-9174-e86a75e225c8
-- title:
--   Pólya for planar annuli (FLPS 2026, Thm 1.1)
-- statement:
--   Pólya's conjecture for **planar annuli** (Filonov–Levitin–Polterovich–Sher 2026, Theorem 1.1).
--
--   For every inner radius $r\in(0,1)$ and every $k\ge1$, the $k$-th Dirichlet eigenvalue of the annulus $A_r=\{x:r<\|x\|<1\}$ satisfies
--   $$\lambda_k(A_r)\ \ge\ \frac{4\pi k}{|A_r|}\;=\;\frac{4k}{1-r^2}.$$
--   This is the first non-simply-connected planar domain for which the conjecture was verified, and it is directly relevant here because the sought counterexample may have holes. It rules out annuli as counterexamples.
--
--   **Formalization Note.** The annulus is `annulus r` (outer radius normalized to $1$); the bound is written in the uniform Pólya form $4\pi k/\text{area}$, using $|A_r|=\pi(1-r^2)$.
-- source:
--   Filonov–Levitin–Polterovich–Sher, Pólya's conjecture for Dirichlet eigenvalues of annuli, J. London Math. Soc. 113(2) e70425 (2026), Theorem 1.1, https://arxiv.org/abs/2505.21737

import Mathlib
import Definitions.Def_PolyaLaplacian_Spectral
open MeasureTheory Set TopologicalSpace

namespace PolyaLaplacian

theorem polya_annulus (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (k : ℕ) (hk : 1 ≤ k) :
    dirichletEigenvalue (annulus r : Set (EuclideanSpace ℝ (Fin 2))) k ≥
      4 * Real.pi * (k : ℝ) / area (annulus r : Set (EuclideanSpace ℝ (Fin 2))) := by sorry

end PolyaLaplacian
