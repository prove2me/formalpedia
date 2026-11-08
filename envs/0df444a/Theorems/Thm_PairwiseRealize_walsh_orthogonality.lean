-- Prove2me | Theorems.Thm_PairwiseRealize_walsh_orthogonality
-- name    : PairwiseRealize.walsh_orthogonality
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:55:42.373622+00:00
-- url     : https://prove2.me/theorems/cc67f5b7-b871-4e2f-a685-2bcbe6175c11
-- title:
--   §A.1, p.10 — Walsh orthogonality $\sum_{x\in V}v_xv_x^{\mathsf T}=NI_m$
-- statement:
--   Over the full cube, the degree-at-most-two Walsh characters are orthogonal:
--
--   $$\sum_{x\in V}v_xv_x^{\mathsf T}=N\,I_m,\qquad N=2^n.$$
--
--   This is the isotropy behind the moment bound (A.3) for reserve bundles.
--
--   Differences from the source: none.
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.1, p.10 (PDF p.11), and §2.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_PairwiseRealize_Model

namespace PairwiseRealize

/-- **Walsh orthogonality, §2.1 p.3 (PDF p.4) and §A.1 p.10 (PDF p.11).** K. Shi, H. Sun, *Robust
Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256
62090516…): "the coordinates of v_x are low-degree Walsh characters, which are orthogonal over the
full cube" (p.3); "Indeed EX_C = aI_m by Walsh orthogonality" (p.10). Over the full cube,

`Σ_{x∈V} v_x v_xᵀ = N I_m`, `N = 2ⁿ`. -/
theorem walsh_orthogonality (n : ℕ) :
    ∑ x : Row n, Matrix.vecMulVec (vR n x) (vR n x) =
      (2 ^ n : ℝ) • (1 : Matrix (Feat n) (Feat n) ℝ) := by sorry

end PairwiseRealize
