-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_exampleDistance
-- name    : QAlgorithms.Papers.Independent.Information100.P10.exampleDistance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:41:48.837209+00:00
-- url     : https://prove2.me/theorems/885ec984-770e-45e6-9234-3833ee3aeaa6
-- title:
--   Three-qubit example: closed entanglement-distance formula, Eq.(47)
-- statement:
--   For $\theta,\phi\in[0,\pi/2]$, the three-qubit vector $\psi(\theta,\phi)=\cos\phi\cos\theta|000\rangle+\cos\phi\sin\theta|110\rangle+\sin\phi\cos\theta|011\rangle-\sin\phi\sin\theta|111\rangle$ is normalized and has entanglement distance
--
--   $$E(\psi(\theta,\phi))=3-\frac{31-8\cos(2\theta)+9\cos(4\theta)-4\cos^2\theta\cos(4\phi)(\cos(2\theta)-5)-16\cos(2\phi)\sin^2(2\theta)}{16}.$$
--
--   This evaluates the geometrically defined ED throughout the displayed two-parameter family; Figure 1 illustrates the same formula.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 5, Three-qubit example: closed entanglement-distance formula, Eq.(47)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF p.5, Eq.(47), illustrated on p.6: the complete trigonometric formula.
The factor (cos(2 theta)-5) multiplies -4 cos(theta)^2 cos(4 phi). -/
theorem exampleDistance (theta phi : ℝ)
    (htheta : theta ∈ Set.Icc 0 (Real.pi / 2))
    (hphi : phi ∈ Set.Icc 0 (Real.pi / 2)) :
    IsState (threeQubitFamily theta phi) ∧
    entanglementDistance (threeQubitFamily theta phi) = 3 -
      (31 - 8 * Real.cos (2 * theta) + 9 * Real.cos (4 * theta) -
        4 * Real.cos theta ^ 2 * Real.cos (4 * phi) * (Real.cos (2 * theta) - 5) -
        16 * Real.cos (2 * phi) * Real.sin (2 * theta) ^ 2) / 16 := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
