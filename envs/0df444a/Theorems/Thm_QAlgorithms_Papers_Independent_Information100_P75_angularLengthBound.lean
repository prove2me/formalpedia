-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_angularLengthBound
-- name    : QAlgorithms.Papers.Independent.Information100.P75.angularLengthBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:15:51.469572+00:00
-- url     : https://prove2.me/theorems/466af9df-58b6-4746-9feb-70bff2e8363c
-- title:
--   Angular feasibility length is at most pi for a nonzero matrix
-- statement:
--   Let $n\ge1$ and $0\ne A\in M_n(\mathbb C)$. Define $\Gamma_A=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}A)\succeq0\}$ and let $|\Gamma_A|$ denote its Lebesgue length in radians. Then
--
--   $$|\Gamma_A|\le\pi.$$
--
--   The nonzero condition is essential: $\Gamma_0=[-\pi,\pi)$ has length $2\pi$. The bound puts the overlined width of nonzero matrices in $[0,\pi]$.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 6, Appendix B opening

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Appendix B opening, PDF p.6: nonzero is essential, since Γ_0 has length 2π. -/
theorem angularLengthBound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Mat ι) (hX : X ≠ 0) : gammaLength X ≤ Real.pi := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
