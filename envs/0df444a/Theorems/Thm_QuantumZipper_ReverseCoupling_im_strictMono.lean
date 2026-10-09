-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_im_strictMono
-- name    : QuantumZipper.ReverseCoupling.im_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:20.374983+00:00
-- url     : https://prove2.me/theorems/b61f20ab-96f7-4adb-9d46-c279941a4209
-- title:
--   §4.1, p. 48 — Im f_t(z) is strictly increasing in t
-- statement:
--   Let $W$ be a continuous driving function and $f_t$ the reverse Loewner flow driven by $W$. For every $z\in\mathbb H$, the function
--   $$t\longmapsto\operatorname{Im}f_t(z),\qquad t\ge0,$$
--   is strictly increasing.
--
--   This is what keeps the reverse flow inside $\mathbb H$ and underlies the uniform bound on $\partial_tC_t(z)$.
--
--   **Formalization Note** Pathwise, for every continuous driver. Since $W$ is real, $\operatorname{Im}f_t=\operatorname{Im}g_t$.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 48 (parenthetical remark)

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **§4.1, p. 48** (unnumbered): "(Note that `Im f_t(z)` is strictly increasing in `t`.)"
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 48.

For a continuous driving function `W` and the reverse Loewner flow `f_t = g_t − W_t`, for every
`z ∈ ℍ` the map `t ↦ Im f_t(z)` is strictly increasing on `[0, ∞)`.

**Formalization Note** Pathwise, for every continuous driver; `Im f_t = Im g_t` because `W` is real. -/
theorem im_strictMono (W : ℝ≥0 → ℝ) (hW : Continuous W) (g : ℝ≥0 → ℂ → ℂ)
    (hg : IsReverseLoewnerFlow W g) (z : ℂ) (hz : 0 < z.im) :
    StrictMono fun t : ℝ≥0 => (revF W g t z).im := by sorry

end QuantumZipper.ReverseCoupling
