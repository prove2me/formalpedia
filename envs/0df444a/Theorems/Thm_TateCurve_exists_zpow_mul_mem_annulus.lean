-- Prove2me | Theorems.Thm_TateCurve_exists_zpow_mul_mem_annulus
-- name    : TateCurve.exists_zpow_mul_mem_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/9a717bce-2579-5eca-b831-2e85879b7df6
-- title:
--   A q^ℤ-translate in the Tate annulus
-- statement:
--   Let $K$ be a nontrivially normed field and let $q, u \in K$ with $q \neq 0$, $\|q\| < 1$ (the inequality being stated for the $\mathbb{R}_{\geq 0}$-valued norm $\|\cdot\|_{+}$) and $u \neq 0$. The assertion is that there exists an integer $n$ such that, writing $v = q^{n} u$, both $\|q v\| < 1$ and $\|q v^{-1}\| < 1$ hold (again as inequalities of non-negative real norms). Since $q$ and $u$ are non-zero, $v$ is non-zero and the two conditions say exactly that $\|q\| < \|v\| < \|q\|^{-1}$, i.e. that the $q^{\mathbb{Z}}$-orbit of $u$ meets the open annulus cut out by these two inequalities. No ultrametric hypothesis on the norm of $K$ is imposed; the multiplicativity of the norm on the field is all that is used.
--
--   This is the elementary input to the Tate parametrisation: the region $\|q\| < \|v\| < \|q\|^{-1}$ is where the $q$-expansions defining the coordinates of the Tate curve are handled, and the statement says that every non-zero $u$ may be normalised into it by a power of $q$. It is used in the verification that the normalised point satisfies the Tate curve equation and in the associated export lemmas.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_exists_zpow_mul_mem_annulus.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal

theorem TateCurve.exists_zpow_mul_mem_annulus {K : Type*} [NontriviallyNormedField K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) : ∃ n : ℤ, ‖q * (q ^ n * u)‖₊ < 1 ∧ ‖q * (q ^ n * u)⁻¹‖₊ < 1 := by sorry
