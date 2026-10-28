-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P34_mziScattering
-- name    : QAlgorithms.Papers.Independent.Dependency50.P34.mziScattering
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:21:54.490193+00:00
-- url     : https://prove2.me/theorems/721f9d0a-bf2e-432b-b488-50bf2e38212a
-- title:
--   MZI composition and full reciprocity relations
-- statement:
--   Let $\theta\in\mathbb R$ and let the two lossless splitter matrices, in the geometric orientations of the interferometer, be
--   $$
--   B_1=\begin{pmatrix}t'_1&r_1\\r'_1&t_1\end{pmatrix},\qquad
--   B_2=\begin{pmatrix}t_2&r'_2\\r_2&t'_2\end{pmatrix},
--   $$
--   with all eight coefficients complex and both matrices unitary. Put $z=e^{i\theta}$. The MZI matrix is
--   $$
--   M=B_2\operatorname{diag}(1,z)B_1
--    =\begin{pmatrix}t'_M&r_M\\r'_M&t_M\end{pmatrix},
--   $$
--   where
--   $$
--   \begin{aligned}
--   t'_M&=t'_1t_2+zr'_1r'_2,&r_M&=r_1t_2+zt_1r'_2,\\
--   r'_M&=t'_1r_2+zr'_1t'_2,&t_M&=r_1r_2+zt_1t'_2.
--   \end{aligned}
--   $$
--   Moreover, $M$ is unitary and satisfies every reciprocity relation:
--   $$
--   |r'_M|=|r_M|,\quad |t_M|=|t'_M|,\quad
--   |r_M|^2+|t_M|^2=1,\quad
--   \overline{r_M}t'_M+r'_M\overline{t_M}=0.
--   $$
--   The identity identifies the two-path interferometer with a single passive lossless four-port device. It is independent of the incident quantum state.
-- source:
--   Quantum Interference between a Single-Photon Fock State and a Coherent State, arXiv:1009.1844v2, PDF p. 6, §III/A, Eqs.(21)–(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P34

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Dependency50.P34

/-- arXiv:1009.1844v2, PDF pp.5–6, §III/A, Eqs.(21)–(22).
Composition has the four stated entries, is unitary, and obeys every reciprocity
relation of Eq.(2). The second splitter is oriented as in Eq.(21).
No condition on a quantum input is needed for this scattering-matrix identity. -/
theorem mziScattering
    (t1Prime r1 r1Prime t1 t2 r2Prime r2 t2Prime : ℂ) (theta : ℝ)
    (h1 : beamMatrix t1Prime r1 r1Prime t1 ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (h2 : beamMatrix t2 r2Prime r2 t2Prime ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    let z := Complex.exp (Complex.I * (theta : ℂ))
    let tMPrime := t1Prime * t2 + z * r1Prime * r2Prime
    let rM := r1 * t2 + z * t1 * r2Prime
    let rMPrime := t1Prime * r2 + z * r1Prime * t2Prime
    let tM := r1 * r2 + z * t1 * t2Prime
    let M := mziMatrix (beamMatrix t1Prime r1 r1Prime t1)
      (beamMatrix t2 r2Prime r2 t2Prime) theta
    M = beamMatrix tMPrime rM rMPrime tM ∧
      M ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      ‖rMPrime‖ = ‖rM‖ ∧ ‖tM‖ = ‖tMPrime‖ ∧
      ‖rM‖ ^ 2 + ‖tM‖ ^ 2 = 1 ∧
      star rM * tMPrime + rMPrime * star tM = 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P34

end
