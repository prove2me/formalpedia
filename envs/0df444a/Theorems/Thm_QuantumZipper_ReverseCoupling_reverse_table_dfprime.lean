-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_reverse_table_dfprime
-- name    : QuantumZipper.ReverseCoupling.reverse_table_dfprime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:34.783632+00:00
-- url     : https://prove2.me/theorems/5acd2e35-3d3d-4963-9be0-214bba7067fa
-- title:
--   §4.1, reverse-flow table, p. 44 — df′_t(z) = 2f′_t(z)/f_t(z)² dt
-- statement:
--   Let $W$ be a continuous driving function and $f_t=g_t-W_t$ the reverse Loewner flow driven by $W$. For every $z\in\mathbb H$ and $t\ge0$, the map $t\mapsto f'_t(z)$ is differentiable (from the right at $t=0$) and
--   $$\frac{d}{dt}f'_t(z)=\frac{2f'_t(z)}{f_t(z)^2},\qquad\text{equivalently}\qquad d\log f'_t(z)=\frac{2}{f_t(z)^2}\,dt .$$
--
--   This is the reverse-flow entry of the table of time derivatives on p. 44; together with $d\mathfrak h^*_t$ it is the input to every martingale computation of §4.1.
--
--   **Formalization Note** Stated pathwise for every continuous driver; the paper's driver $W_t=\sqrt\kappa B_t$ is a sample of one. The driving term does not enter $f'_t=\partial_zg_t$, so this is an ordinary derivative. The branch-free $df'$ row is stated.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, reverse-flow table (REVERSE FLOW SLE column, rows 3–4), p. 44

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **§4.1, reverse-flow table, p. 44** (unnumbered; REVERSE FLOW SLE column, rows 3–4):
`df′_t(z) = 2 f′_t(z)/f_t(z)² dt`, equivalently `d log f′_t(z) = 2/f_t(z)² dt`.
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, reverse-flow table, p. 44.

For a continuous driving function `W` and the reverse Loewner flow `f_t = g_t − W_t`, for every
`z ∈ ℍ` and `t ≥ 0` the map `t ↦ f′_t(z)` is differentiable (right derivative at `t = 0`) with
derivative `2 f′_t(z)/f_t(z)²`.

**Formalization Note** Stated pathwise for every continuous driver `W` (the paper's `W_t = √κ B_t`
is one sample of such a driver); `W` does not enter `f′_t = ∂_z g_t`, so this is an ordinary
derivative. The branch-free `df′` row is stated; the `d log f′` row follows from it. -/
theorem reverse_table_dfprime (W : ℝ≥0 → ℝ) (hW : Continuous W) (g : ℝ≥0 → ℂ → ℂ)
    (hg : IsReverseLoewnerFlow W g) (z : ℂ) (hz : 0 < z.im) (t : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => revFDeriv W g (Real.toNNReal s) z)
      (2 * revFDeriv W g t z / revF W g t z ^ 2) (Set.Ici 0) (t : ℝ) := by sorry

end QuantumZipper.ReverseCoupling
