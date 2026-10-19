-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_exampleSeparability
-- name    : QAlgorithms.Papers.Independent.Information100.P10.exampleSeparability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:40:41.574945+00:00
-- url     : https://prove2.me/theorems/731b8f63-5be0-49a3-8857-6e3c975ed39e
-- title:
--   Three-qubit example: boundary separability claims following Eq.(43)
-- statement:
--   For $\theta,\phi\in[0,\pi/2]$, define
--
--   $$\psi(\theta,\phi)=\cos\phi\cos\theta|000\rangle+\cos\phi\sin\theta|110\rangle+\sin\phi\cos\theta|011\rangle-\sin\phi\sin\theta|111\rangle.$$
--
--   This vector is normalized. If $0<\theta<\pi/2$, then $\psi(\theta,0)=(\cos\theta|00\rangle+\sin\theta|11\rangle)\otimes|0\rangle$, where the normalized two-qubit factor is entangled, so the full state is biseparable and not fully separable. The states $\psi(0,0)$ and $\psi(\pi/2,0)$ are fully separable. So are $\psi(\theta,\pi/2)$ for every allowed $\theta$, and $\psi(\pi/2,\phi)$ for every allowed $\phi$. These are precisely the boundary claims made after Eq. (43).
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 5, Three-qubit example: boundary separability claims following Eq.(43)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF p.5, Eqs.(42)-(43) and the full following paragraph: normalization and every
stated boundary separability claim. Interior phi=0 gives an entangled pair times |0>. -/
theorem exampleSeparability (theta phi : ℝ)
    (htheta : theta ∈ Set.Icc 0 (Real.pi / 2))
    (hphi : phi ∈ Set.Icc 0 (Real.pi / 2)) :
    IsState (threeQubitFamily theta phi) ∧
    (0 < theta → theta < Real.pi / 2 →
      IsState (examplePair theta) ∧ ¬ FullySeparable (examplePair theta) ∧
      threeQubitFamily theta 0 = appendKet (examplePair theta) (zeroKet 1) ∧
      ¬ FullySeparable (threeQubitFamily theta 0)) ∧
    FullySeparable (threeQubitFamily 0 0) ∧
    FullySeparable (threeQubitFamily (Real.pi / 2) 0) ∧
    FullySeparable (threeQubitFamily theta (Real.pi / 2)) ∧
    FullySeparable (threeQubitFamily (Real.pi / 2) phi) := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
