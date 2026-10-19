-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_exampleBlochVectors
-- name    : QAlgorithms.Papers.Independent.Information100.P10.exampleBlochVectors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:41:08.929968+00:00
-- url     : https://prove2.me/theorems/7de585f4-d295-4cb1-9fa7-70685dc3e228
-- title:
--   Three-qubit example: the nine Pauli expectations, Eqs.(44)–(46)
-- statement:
--   For the three-qubit vector $\psi(\theta,\phi)=\cos\phi\cos\theta|000\rangle+\cos\phi\sin\theta|110\rangle+\sin\phi\cos\theta|011\rangle-\sin\phi\sin\theta|111\rangle$, with $\theta,\phi\in[0,\pi/2]$, write $c_1=\cos\theta$, $s_1=\sin\theta$, $c_2=\cos\phi$, $s_2=\sin\phi$. The vector is normalized. Write $r_\mu=(\langle\psi|X_\mu|\psi\rangle,\langle\psi|Y_\mu|\psi\rangle,\langle\psi|Z_\mu|\psi\rangle)$. In $X,Y,Z$ order these vectors are
--
--   $$r_0=(-2c_1s_1s_2^2,0,c_1^2-s_1^2),\quad r_1=(0,0,(c_1^2-s_1^2)c_2^2-s_2^2),\quad r_2=(-2s_1^2s_2c_2,0,c_2^2-s_2^2).$$
--
--   The source's qubits 1,2,3 correspond to wires 0,1,2. These nine expectations supply the ED formula for this explicit family.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 5, Three-qubit example: the nine Pauli expectations, Eqs.(44)–(46)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF p.5, Eqs.(44)-(46): all nine local Pauli expectations, on wires 0,1,2. -/
theorem exampleBlochVectors (theta phi : ℝ)
    (htheta : theta ∈ Set.Icc 0 (Real.pi / 2))
    (hphi : phi ∈ Set.Icc 0 (Real.pi / 2)) :
    IsState (threeQubitFamily theta phi) ∧
    bloch (threeQubitFamily theta phi) 0 = WithLp.toLp 2
      ![-2 * Real.cos theta * Real.sin theta * Real.sin phi ^ 2,
        0, Real.cos theta ^ 2 - Real.sin theta ^ 2] ∧
    bloch (threeQubitFamily theta phi) 1 = WithLp.toLp 2
      ![0, 0, (Real.cos theta ^ 2 - Real.sin theta ^ 2) * Real.cos phi ^ 2 -
        Real.sin phi ^ 2] ∧
    bloch (threeQubitFamily theta phi) 2 = WithLp.toLp 2
      ![-2 * Real.sin theta ^ 2 * Real.sin phi * Real.cos phi,
        0, Real.cos phi ^ 2 - Real.sin phi ^ 2] := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
