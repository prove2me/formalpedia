-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_reverse_table_dGt
-- name    : QuantumZipper.ReverseCoupling.reverse_table_dGt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:05.059577+00:00
-- url     : https://prove2.me/theorems/8cff7ccc-2c96-4b23-9891-6c97114af6a8
-- title:
--   §4.1, reverse-flow table, p. 47 — dG_t(y,z) = −Re(2/f_t(y)) Re(2/f_t(z)) dt
-- statement:
--   Let $W$ be a continuous driving function and $f_t$ the reverse Loewner flow driven by $W$. Let $G(y,z)=-\log|y-z|-\log|y-\bar z|$ and $G_t(y,z)=G(f_t(y),f_t(z))$. For all $y\neq z$ in $\mathbb H$ and $t\ge0$, $t\mapsto G_t(y,z)$ is differentiable (from the right at $t=0$) and
--   $$\frac{d}{dt}G_t(y,z)=-\operatorname{Re}\frac{2}{f_t(y)}\,\operatorname{Re}\frac{2}{f_t(z)} .$$
--
--   Combined with $d\mathfrak h_t(z)=\operatorname{Re}\frac{-2}{f_t(z)}dB_t$ this gives $d\langle\mathfrak h_t(y),\mathfrak h_t(z)\rangle=-dG_t(y,z)$, the reverse-flow identity on p. 47.
--
--   **Formalization Note** Pathwise for every continuous driver. The Brownian increments cancel in $f_t(y)-f_t(z)$ and $f_t(y)-\overline{f_t(z)}$, so $G_t$ has an ordinary time derivative. The hypothesis $y\neq z$ is implicit on the page.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, reverse-flow table (REVERSE FLOW SLE column, rows 1–3), p. 47

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **§4.1, reverse-flow table, p. 47** (unnumbered; REVERSE FLOW SLE column, rows 1–3):
`G(y, z) = −log |y − z| − log |y − z̄|`, `G_t(y, z) = G(f_t(y), f_t(z))`,
`dG_t(y, z) = −Re(2/f_t(y)) Re(2/f_t(z)) dt`.
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, reverse-flow table, p. 47.

For a continuous driving function `W` and the reverse Loewner flow, for all `y ≠ z` in `ℍ` and
`t ≥ 0`, `t ↦ G_t(y, z)` is differentiable (right derivative at `t = 0`) with derivative
`−Re(2/f_t(y)) · Re(2/f_t(z))`.

**Formalization Note** Pathwise, for every continuous driver. The `√κ dB_t` terms cancel in
`f_t(y) − f_t(z)` and `f_t(y) − conj f_t(z)`, so `G_t` has an ordinary time derivative. The hypothesis
`y ≠ z` is implicit on the page (`G` is singular on the diagonal). -/
theorem reverse_table_dGt (W : ℝ≥0 → ℝ) (hW : Continuous W) (g : ℝ≥0 → ℂ → ℂ)
    (hg : IsReverseLoewnerFlow W g) (y z : ℂ) (hy : 0 < y.im) (hz : 0 < z.im) (hyz : y ≠ z)
    (t : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => Gt W g (Real.toNNReal s) y z)
      (-((2 / revF W g t y).re * (2 / revF W g t z).re)) (Set.Ici 0) (t : ℝ) := by sorry

end QuantumZipper.ReverseCoupling
